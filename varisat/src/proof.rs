//! Proof generation.

use std::borrow::Cow;
use std::io::{sink, BufWriter, Write};

use serde::{Deserialize, Serialize};

use crate::checker::{Checker, ProofProcessor};
use crate::lit::Lit;

/// Proof formats that can be generated during solving.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum ProofFormat {
    Varisat,
    Drat,
    BinaryDrat,
}

/// Integer type used to store a hash of a clause.
pub type ClauseHash = u64;

/// Hash a single literal.
///
/// Multiple literals can be combined with xor, as done in [`clause_hash`].
pub fn lit_hash(lit: Lit) -> ClauseHash {
    // Constant based on the golden ratio provides good mixing for the resulting upper bits
    (!(lit.code() as u64)).wrapping_mul(0x61c8864680b583ebu64)
}

/// A fast hash function for clauses (or other *sets* of literals).
///
/// This hash function interprets the given slice as a set and will not change when the input is
/// permuted. It does not handle duplicated items.
pub fn clause_hash(lits: &[Lit]) -> ClauseHash {
    let mut hash = 0;
    for &lit in lits {
        hash ^= lit_hash(lit);
    }
    hash
}

/// A single proof step.
///
/// Represents a mutation of the current formula and a justification for the mutation's validity.
#[derive(Clone, Serialize, Deserialize, Debug)]
pub enum ProofStep<'a> {
    /// Add a clause that is an asymmetric tautoligy (AT).
    ///
    /// Assuming the negation of the clause's literals leads to a unit propagation conflict.
    ///
    /// The second slice contains the hashes of all clauses involved in the resulting conflict. The
    /// order of hashes is the order in which the clauses propagate when all literals of the clause
    /// are set false.
    ///
    /// When generating DRAT proofs the second slice is ignored and may be empty.
    AtClause {
        clause: Cow<'a, [Lit]>,
        propagation_hashes: Cow<'a, [ClauseHash]>,
    },
    /// Unit clauses found by top-level unit-propagation.
    ///
    /// Pairs of unit clauses and the original clause that became unit. Clauses are in chronological
    /// order. This is equivalent to multiple `AtClause` steps where the clause is unit and the
    /// propagation_hashes field contains just one hash, with the difference that this is not output
    /// for DRAT proofs.
    ///
    /// Ignored when generating DRAT proofs.
    UnitClauses(Cow<'a, [(Lit, ClauseHash)]>),
    /// Delete a clause consisting of the given literals.
    DeleteClause(Cow<'a, [Lit]>),
}

/// Proof generation.
pub struct Proof<'a> {
    format: Option<ProofFormat>,
    target: BufWriter<Box<dyn Write + 'a>>,
    checker: Option<Checker<'a>>,
}

impl<'a> Default for Proof<'a> {
    fn default() -> Proof<'a> {
        Proof {
            format: None,
            target: BufWriter::new(Box::new(sink())),
            checker: None,
        }
    }
}

macro_rules! handle_io_errors {
    ($s:expr, $e:expr) => {{
        let res = $e;
        $s.handle_io_errors(res)
    }};
}

impl<'a> Proof<'a> {
    /// Start writing proof steps to the given target with the given format.
    pub fn write_proof(&mut self, target: impl Write + 'a, format: ProofFormat) {
        self.format = Some(format);
        self.target = BufWriter::new(Box::new(target))
    }

    /// Stop writing proof steps.
    pub fn close_proof(&mut self) {
        // We need to explicitly flush to handle IO errors.
        handle_io_errors!(self, self.target.flush());
        self.format = None;
        self.target = BufWriter::new(Box::new(sink()));
    }

    /// Begin checking proof steps.
    pub fn begin_checking(&mut self) {
        if self.checker.is_none() {
            self.checker = Some(Checker::new())
        }
    }

    /// Called before solve returns to trigger delayed unit conflict processing.
    pub fn solve_finished(&mut self) {
        if let Some(checker) = &mut self.checker {
            checker.process_unit_conflicts().unwrap();
            // TODO error handling
        }
    }

    /// Add a [`ProofProcessor`].
    ///
    /// See also [`Checker::add_processor`].
    pub fn add_processor(&mut self, processor: &'a mut dyn ProofProcessor) {
        self.begin_checking();
        self.checker.as_mut().unwrap().add_processor(processor);
    }

    /// Whether proof generation is active.
    pub fn is_active(&self) -> bool {
        self.checker.is_some() || self.format.is_some()
    }

    /// Whether clause hashes are required for steps that support them.
    pub fn clause_hashes_required(&self) -> bool {
        self.checker.is_some()
            || match self.format {
                Some(ProofFormat::Varisat) => true,
                Some(ProofFormat::Drat) | Some(ProofFormat::BinaryDrat) => false,
                None => false,
            }
    }

    /// Whether unit clauses discovered through unit propagation have to be proven.
    pub fn prove_propagated_unit_clauses(&self) -> bool {
        self.checker.is_some()
            || match self.format {
                Some(ProofFormat::Varisat) => true,
                Some(ProofFormat::Drat) | Some(ProofFormat::BinaryDrat) => false,
                None => false,
            }
    }

    /// Add a step to the proof.
    ///
    /// Ignored when proof generation is disabled.
    pub fn add_step<'s>(&'s mut self, step: &'s ProofStep<'s>) {
        match self.format {
            None => (),
            Some(ProofFormat::Varisat) => self.write_varisat_step(step),
            Some(ProofFormat::Drat) | Some(ProofFormat::BinaryDrat) => self.write_drat_step(step),
        }
        if let Some(checker) = &mut self.checker {
            checker.check_step(step.clone()).unwrap();
            // TODO error handling
        }
    }

    /// Call when adding an external clause.
    ///
    /// This is ignored for writing proof files but required for on-the-fly checking.
    pub fn add_clause(&mut self, clause: &[Lit]) {
        if let Some(checker) = &mut self.checker {
            checker.add_clause(clause).unwrap();
            // TODO error handling
        }
    }

    /// Writes a proof step in our own format.
    fn write_varisat_step<'s>(&'s mut self, step: &'s ProofStep<'s>) {
        handle_io_errors!(self, bincode::serialize_into(&mut self.target, step));
    }

    /// Writes a proof step in DRAT or binary DRAT format.
    fn write_drat_step<'s>(&'s mut self, step: &'s ProofStep<'s>) {
        match step {
            ProofStep::AtClause { clause, .. } => {
                self.drat_add_clause();
                self.drat_literals(&clause)
            }
            ProofStep::DeleteClause(clause) => {
                self.drat_delete_clause();
                self.drat_literals(&clause[..]);
            }
            ProofStep::UnitClauses(..) => (),
        }
    }

    /// Writes an add clause step to the DRAT proof.
    fn drat_add_clause(&mut self) {
        if self.format == Some(ProofFormat::BinaryDrat) {
            handle_io_errors!(self, self.target.write_all(b"a"));
        }
    }

    /// Writes a delete clause step to the DRAT proof.
    fn drat_delete_clause(&mut self) {
        if self.format == Some(ProofFormat::BinaryDrat) {
            handle_io_errors!(self, self.target.write_all(b"d"));
        } else {
            handle_io_errors!(self, self.target.write_all(b"d "));
        }
    }

    /// Writes the literals of a clause for a step in a DRAT proof.
    fn drat_literals(&mut self, literals: &[Lit]) {
        if self.format == Some(ProofFormat::BinaryDrat) {
            for &lit in literals {
                let drat_code = lit.code() as u64 + 2;
                handle_io_errors!(self, leb128::write::unsigned(&mut self.target, drat_code));
            }
            handle_io_errors!(self, self.target.write_all(&[0]));
        } else {
            for &lit in literals {
                handle_io_errors!(self, itoa::write(&mut self.target, lit.to_dimacs()));
                handle_io_errors!(self, self.target.write_all(b" "));
            }
            handle_io_errors!(self, self.target.write_all(b"0\n"));
        }
    }

    /// Handles IO errors.
    ///
    /// Right now this panics. In the future it should set an error flag that will be checked in the
    /// solver main loop to abort when proof writing failed.
    fn handle_io_errors<V, E: std::fmt::Debug>(&self, result: Result<V, E>) -> Option<V> {
        // TODO better error handling
        // on error we want to abort solving eventually but not panic
        // we also don't want to force error handling on proof generating code
        Some(result.expect("unable to write to proof file"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;

    use std::fs::File;
    use std::process::Command;

    use tempfile::TempDir;

    use crate::dimacs::write_dimacs;
    use crate::solver::Solver;

    use crate::test::sgen_unsat_formula;

    proptest! {

        #[cfg_attr(not(test_drat_trim), ignore)]
        #[test]
        fn sgen_unsat_drat(
            formula in sgen_unsat_formula(1..7usize),
        ) {
            let mut solver = Solver::new();

            let tmp = TempDir::new()?;

            let drat_proof = tmp.path().join("proof.drat");
            let cnf_file = tmp.path().join("input.cnf");

            write_dimacs(&mut File::create(&cnf_file)?, &formula)?;

            solver.write_proof(File::create(&drat_proof)?, ProofFormat::Drat);

            solver.add_formula(&formula);

            prop_assert_eq!(solver.solve(), Some(false));

            solver.close_proof();

            let output = Command::new("drat-trim")
                .arg(&cnf_file)
                .arg(&drat_proof)
                .output()?;

            prop_assert!(std::str::from_utf8(&output.stdout)?.contains("s VERIFIED"));
        }

        #[cfg_attr(not(test_drat_trim), ignore)]
        #[test]
        fn sgen_unsat_binary_drat(
            formula in sgen_unsat_formula(1..7usize),
        ) {
            let mut solver = Solver::new();

            let tmp = TempDir::new()?;

            let drat_proof = tmp.path().join("proof.bdrat");
            let cnf_file = tmp.path().join("input.cnf");

            write_dimacs(&mut File::create(&cnf_file)?, &formula)?;

            solver.write_proof(File::create(&drat_proof)?, ProofFormat::BinaryDrat);

            solver.add_formula(&formula);

            prop_assert_eq!(solver.solve(), Some(false));

            solver.close_proof();

            let output = Command::new("drat-trim")
                .arg(&cnf_file)
                .arg(&drat_proof)
                .arg("-i")
                .output()?;

            prop_assert!(std::str::from_utf8(&output.stdout)?.contains("s VERIFIED"));
        }
    }
}
