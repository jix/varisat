//! Check unsatisfiability proofs.

use std::io;

use failure::{Error, Fail};
use hashbrown::HashMap;
use smallvec::SmallVec;

use crate::cnf::CnfFormula;
use crate::dimacs::DimacsParser;
use crate::lit::Lit;
use crate::proof::{clause_hash, ClauseHash, ProofStep};

/// Possible errors while checking a varisat proof.
#[derive(Debug, Fail)]
pub enum CheckerError {
    #[fail(
        display = "step {}: Proof ended without deriving unsatisfiability",
        step
    )]
    ProofIncomplete { step: u64 },
    #[fail(display = "step {}: Could not parse proof step: {}", step, cause)]
    PraseError {
        step: u64,
        #[cause]
        cause: Error,
    },
    #[fail(display = "step {}: Delete of unknown clause {:?}", step, clause)]
    InvalidDelete { step: u64, clause: Vec<Lit> },
    #[fail(display = "step {}: No clause with hash {:x} found", step, hash)]
    ClauseNotFound { step: u64, hash: ClauseHash },
    #[fail(display = "step {}: Checking proof for {:?} failed", step, clause)]
    ClauseCheckFailed { step: u64, clause: Vec<Lit> },
    #[doc(hidden)]
    #[fail(display = "__Nonexhaustive")]
    __Nonexhaustive,
}

/// Avoid indirection for small clauses.
type LitVec = SmallVec<[Lit; 4]>;

/// Literals and metadata for non-unit clauses.
#[derive(Debug)]
struct Clause {
    /// LRAT clause id.
    id: u64,
    /// How often the clause is present.
    ///
    /// For checking the formula is a multiset of clauses. This is necessary as the generating
    /// solver might not check for duplicated clauses.
    ref_count: u32,
    /// Clause's literals.
    lits: LitVec,
}

/// A checker for unsatisfiability proofs in the native varisat format.
#[derive(Default)]
pub struct Checker {
    /// Current step number.
    step: u64,
    /// Last used LRAT caluse id.
    last_clause_id: u64,
    /// Stores all known non-unit clauses indexed by their hash.
    clauses: HashMap<ClauseHash, SmallVec<[Clause; 1]>>,
    /// Stores known unit clauses and propagations during a clause check.
    unit_clauses: Vec<Option<(bool, u64)>>,
    /// Stores overwritten values in `unit_clauses` to undo assignments.
    trail: Vec<(Lit, Option<(bool, u64)>)>,
    /// Whether unsatisfiability was proven.
    unsat: bool,
}

impl Checker {
    /// Create a new checker.
    pub fn new() -> Checker {
        Checker::default()
    }

    /// Add a formula to the checker.
    pub fn add_formula(&mut self, formula: &CnfFormula) {
        for clause in formula.iter() {
            self.add_clause(clause);
        }
    }

    /// Adds a clause to the checker.
    pub fn add_clause(&mut self, clause: &[Lit]) {
        let mut lits = LitVec::from_slice(clause);
        lits.sort_unstable();
        lits.dedup();

        self.store_clause(lits);
    }

    /// Reads and adds a formula in DIMACS CNF format.
    ///
    /// Using this avoids creating a temporary [`CnfFormula`].
    pub fn add_dimacs_cnf(&mut self, input: impl io::Read) -> Result<(), Error> {
        // TODO avoid code duplication with Solver's add_dimacs_cnf
        use io::BufRead;

        let mut buffer = io::BufReader::new(input);
        let mut parser = DimacsParser::new();

        loop {
            let data = buffer.fill_buf()?;
            if data.is_empty() {
                break;
            }
            parser.parse_chunk(data)?;
            let len = data.len();
            buffer.consume(len);

            self.add_formula(&parser.take_formula());
        }
        parser.eof()?;
        self.add_formula(&parser.take_formula());
        parser.check_header()?;

        log::info!(
            "Parsed formula with {} variables and {} clauses",
            parser.var_count(),
            parser.clause_count()
        );

        Ok(())
    }

    /// Value of a literal if known from unit clauses.
    fn lit_value(&self, lit: Lit) -> Option<(bool, u64)> {
        self.unit_clauses
            .get(lit.index())
            .and_then(|&value| value)
            .map(|(polarity, id)| (polarity ^ lit.is_negative(), id))
    }

    /// Adds a clause to the checker data structures.
    ///
    /// `lits` must be sorted and free of duplicates.
    fn store_clause(&mut self, lits: LitVec) {
        match lits[..] {
            [] => self.unsat = true,
            [lit] => self.store_unit_clause(lit),
            _ => {
                let hash = clause_hash(&lits);

                let candidates = self.clauses.entry(hash).or_default();

                for candidate in candidates.iter_mut() {
                    if candidate.lits == lits {
                        candidate.ref_count += 1;
                        return;
                    }
                }

                self.last_clause_id += 1;

                candidates.push(Clause {
                    id: self.last_clause_id,
                    ref_count: 1,
                    lits,
                })
            }
        }
    }

    /// Adds a unit clause to the checker data structures.
    fn store_unit_clause(&mut self, lit: Lit) {
        match self.lit_value(lit) {
            Some((true, _)) => (),
            Some((false, _)) => self.unsat = true, // TODO lrat output
            None => {
                self.last_clause_id += 1;

                if self.unit_clauses.len() <= lit.index() {
                    self.unit_clauses.resize(lit.index() + 1, None);
                }

                self.unit_clauses[lit.index()] = Some((lit.is_positive(), self.last_clause_id));
            }
        }
    }

    /// Delete a clause from the current formula.
    ///
    /// `lits` must be sorted and free of duplicates.
    fn delete_clause(&mut self, lits: &[Lit]) -> Result<(), CheckerError> {
        if lits.len() < 2 {
            return Err(CheckerError::InvalidDelete {
                step: self.step,
                clause: lits.to_owned(),
            });
        }

        let hash = clause_hash(lits);

        let candidates = self.clauses.entry(hash).or_default();

        let mut deleted = false;

        candidates.retain(|candidate| {
            if deleted || &candidate.lits[..] != lits {
                true
            } else {
                deleted = true;
                candidate.ref_count -= 1;
                candidate.ref_count > 0
            }
        });

        if candidates.is_empty() {
            self.clauses.remove(&hash);
        }

        if !deleted {
            return Err(CheckerError::InvalidDelete {
                step: self.step,
                clause: lits.to_owned(),
            });
        } else {
            Ok(())
        }
    }

    /// Check whether a clause is implied by clauses of the given hashes.
    ///
    /// `lits` must be sorted and free of duplicates.
    fn check_clause_with_hashes(
        &mut self,
        lits: &[Lit],
        clause_hashes: &[ClauseHash],
    ) -> Result<Vec<u64>, CheckerError> {
        let mut trace = vec![];

        let mut result = None;

        assert!(self.trail.is_empty());

        // Set all lits to false
        for &lit in lits.iter() {
            if self.unit_clauses.len() <= lit.index() {
                self.unit_clauses.resize(lit.index() + 1, None);
            }

            self.trail.push((lit, self.unit_clauses[lit.index()]));

            self.unit_clauses[lit.index()] = Some((lit.is_negative(), 0));
        }

        'hashes: for &hash in clause_hashes.iter() {
            let candidates = match self.clauses.get(&hash) {
                Some(candidates) if !candidates.is_empty() => candidates,
                _ => {
                    return Err(CheckerError::ClauseNotFound {
                        step: self.step,
                        hash,
                    })
                }
            };

            // Check if any clause matching the hash propagates
            'candidates: for clause in candidates.iter() {
                let mut unassigned_count = 0;
                let mut unassigned_lit = None;

                for &lit in clause.lits.iter() {
                    match self.lit_value(lit) {
                        Some((true, _)) => {
                            continue 'candidates;
                        }
                        Some((false, id)) => {
                            if id > 0 {
                                trace.push(id);
                                self.trail.push((lit, self.unit_clauses[lit.index()]));
                                self.unit_clauses[lit.index()] = Some((lit.is_negative(), 0));
                            }
                        }
                        None => {
                            unassigned_count += 1;
                            unassigned_lit = Some(lit);
                        }
                    }
                }

                match unassigned_lit {
                    None => {
                        trace.push(clause.id);

                        result = Some(trace);
                        break 'hashes;
                    }
                    Some(lit) if unassigned_count == 1 => {
                        trace.push(clause.id);
                        if self.unit_clauses.len() <= lit.index() {
                            self.unit_clauses.resize(lit.index() + 1, None);
                        }

                        self.trail.push((lit, self.unit_clauses[lit.index()]));

                        self.unit_clauses[lit.index()] = Some((lit.is_positive(), 0));
                    }
                    _ => (),
                }
            }
        }

        // Undo temporary assignments
        for (lit, value) in self.trail.drain(..).rev() {
            self.unit_clauses[lit.index()] = value;
        }

        if let Some(result) = result {
            Ok(result)
        } else {
            Err(CheckerError::ClauseCheckFailed {
                step: self.step,
                clause: lits.to_owned(),
            })
        }
    }

    /// Check a single proof step
    fn check_step(&mut self, step: ProofStep) -> Result<(), CheckerError> {
        match step {
            ProofStep::RupClause(clause, clause_hashes) => {
                let mut clause = LitVec::from_vec(clause.into_owned());
                clause.sort_unstable();
                clause.dedup();

                let _trace = self.check_clause_with_hashes(&clause, &*clause_hashes)?;
                // TODO lrat output
                self.store_clause(clause);
            }
            ProofStep::DeleteClause(clause) => {
                let mut clause = clause.into_owned();
                clause.sort_unstable();
                clause.dedup();

                self.delete_clause(&clause)?;
            }
            ProofStep::UnitClauses(units) => {
                for &(lit, hash) in units.iter() {
                    let clause = [lit];
                    let clause_hashes = [hash];
                    let _trace = self.check_clause_with_hashes(&clause[..], &clause_hashes[..])?;
                    // TODO lrat output
                    self.store_unit_clause(lit);
                }
            }
        }

        Ok(())
    }

    /// Reads and adds a formula in DIMACS CNF format.
    ///
    /// Using this avoids creating a temporary [`CnfFormula`].
    pub fn check_proof(&mut self, input: impl io::Read) -> Result<(), CheckerError> {
        let mut buffer = io::BufReader::new(input);

        while !self.unsat {
            self.step += 1;

            if self.step % 100000 == 0 {
                log::info!("checking step {}k", self.step / 1000);
            }

            match bincode::deserialize_from(&mut buffer) {
                Ok(step) => self.check_step(step)?,
                Err(err) => match *err {
                    bincode::ErrorKind::Io(ref io_err)
                        if io_err.kind() == io::ErrorKind::UnexpectedEof =>
                    {
                        return Err(CheckerError::ProofIncomplete { step: self.step })
                    }
                    _ => {
                        return Err(CheckerError::PraseError {
                            step: self.step,
                            cause: err.into(),
                        })
                    }
                },
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;

    use crate::dimacs::write_dimacs;

    use crate::test::io::RcWriteBuffer;
    use crate::test::sgen_unsat_formula;

    use crate::solver::{ProofFormat, Solver};

    #[test]
    fn conflicting_units() {
        let mut checker = Checker::new();

        checker.add_formula(&cnf_formula![
            1;
            -1;
        ]);

        assert!(checker.unsat);
    }

    #[test]
    fn invalid_delete() {
        let mut checker = Checker::new();

        checker.add_formula(&cnf_formula![
            1, 2, 3;
            -4, 5;
        ]);

        match checker.check_step(ProofStep::DeleteClause(lits![-5, 4][..].into())) {
            Err(CheckerError::InvalidDelete { .. }) => (),
            _ => panic!("expected error"),
        }
    }

    #[test]
    fn ref_counts() {
        let mut checker = Checker::new();

        checker.add_formula(&cnf_formula![
            1, 2, 3;
            1, 2, 3;
        ]);

        let lits = &lits![1, 2, 3][..];

        checker
            .check_step(ProofStep::DeleteClause(lits.into()))
            .unwrap();

        checker.add_clause(lits);

        checker
            .check_step(ProofStep::DeleteClause(lits.into()))
            .unwrap();

        checker
            .check_step(ProofStep::DeleteClause(lits.into()))
            .unwrap();

        match checker.check_step(ProofStep::DeleteClause(lits.into())) {
            Err(CheckerError::InvalidDelete { .. }) => (),
            _ => panic!("expected error"),
        }
    }

    #[test]
    fn clause_not_found() {
        let mut checker = Checker::new();
        checker.add_formula(&cnf_formula![
            1, 2, 3;
        ]);

        match checker.check_step(ProofStep::RupClause([][..].into(), [0][..].into())) {
            Err(CheckerError::ClauseNotFound { .. }) => (),
            _ => panic!("expected error"),
        }
    }

    #[test]
    fn clause_check_failed() {
        let mut checker = Checker::new();
        checker.add_formula(&cnf_formula![
            1, 2, 3;
        ]);

        match checker.check_step(ProofStep::RupClause([][..].into(), [][..].into())) {
            Err(CheckerError::ClauseCheckFailed { .. }) => (),
            _ => panic!("expected error"),
        }
    }

    proptest! {
        #[test]
        fn checked_unsat_via_dimacs(formula in sgen_unsat_formula(1..7usize)) {
            let mut solver = Solver::new();

            let mut dimacs = vec![];
            let proof = RcWriteBuffer::default();

            write_dimacs(&mut dimacs, &formula).unwrap();

            solver.write_proof(proof.clone(), ProofFormat::Varisat);

            solver.add_dimacs_cnf(&mut &dimacs[..]).unwrap();

            prop_assert_eq!(solver.solve(), Some(false));

            solver.close_proof();

            let proof = proof.take();

            let mut checker = Checker::new();

            checker.add_dimacs_cnf(&mut &dimacs[..]).unwrap();

            checker.check_proof(&mut &proof[..]).unwrap();
        }
    }
}
