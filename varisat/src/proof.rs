//! Proof generation.

use std::io::{self, sink, BufWriter, Write};

use partial_ref::{partial, PartialRef};

use crate::checker::{Checker, CheckerError, ProofProcessor};
use crate::context::{Context, ProofP, SolverStateP};
use crate::lit::Lit;
use crate::solver::SolverError;

mod drat;
mod map_step;
pub mod varisat;

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

/// Justifications for a simple clause deletion.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum DeleteClauseProof {
    /// The clause is known to be redundant.
    Redundant,
    /// The clause is irred and subsumed by the clause added in the previous step.
    Simplified,
    /// The clause contains a true literal.
    ///
    /// Also used to justify deletion of tautological clauses.
    Satisfied,
}

/// A single proof step.
///
/// Represents a mutation of the current formula and a justification for the mutation's validity.
#[derive(Copy, Clone, Debug)]
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
        redundant: bool,
        clause: &'a [Lit],
        propagation_hashes: &'a [ClauseHash],
    },
    /// Unit clauses found by top-level unit-propagation.
    ///
    /// Pairs of unit clauses and the original clause that became unit. Clauses are in chronological
    /// order. This is equivalent to multiple `AtClause` steps where the clause is unit and the
    /// propagation_hashes field contains just one hash, with the difference that this is not output
    /// for DRAT proofs.
    ///
    /// Ignored when generating DRAT proofs.
    UnitClauses(&'a [(Lit, ClauseHash)]),
    /// Delete a clause consisting of the given literals.
    DeleteClause {
        clause: &'a [Lit],
        proof: DeleteClauseProof,
    },
    /// Change the number of clause hash bits used
    ChangeHashBits(u32),
}

impl<'a> ProofStep<'a> {
    /// Number of added or removed clauses.
    pub fn clause_count_delta(&self) -> isize {
        match self {
            ProofStep::AtClause { clause, .. } => {
                if clause.len() > 1 {
                    1
                } else {
                    0
                }
            }
            ProofStep::DeleteClause { clause, .. } => {
                if clause.len() > 1 {
                    -1
                } else {
                    0
                }
            }

            ProofStep::UnitClauses(..) => 0,
            ProofStep::ChangeHashBits(..) => 0,
        }
    }
}

/// Proof generation.
pub struct Proof<'a> {
    format: Option<ProofFormat>,
    target: BufWriter<Box<dyn Write + 'a>>,
    checker: Option<Checker<'a>>,
    map_step: map_step::MapStep,
    /// How many bits are used for storing clause hashes.
    hash_bits: u32,
    /// How many clauses are currently in the db.
    ///
    /// This is used to pick a good number of hash_bits
    clause_count: isize,
    /// Whether we're finished with the initial loading of clauses.
    initial_load_complete: bool,
}

impl<'a> Default for Proof<'a> {
    fn default() -> Proof<'a> {
        Proof {
            format: None,
            target: BufWriter::new(Box::new(sink())),
            checker: None,
            map_step: Default::default(),
            hash_bits: 64,
            clause_count: 0,
            initial_load_complete: false,
        }
    }
}

impl<'a> Proof<'a> {
    /// Start writing proof steps to the given target with the given format.
    pub fn write_proof(&mut self, target: impl Write + 'a, format: ProofFormat) {
        self.format = Some(format);
        self.target = BufWriter::new(Box::new(target))
    }

    /// Begin checking proof steps.
    pub fn begin_checking(&mut self) {
        if self.checker.is_none() {
            self.checker = Some(Checker::new())
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
}

/// Call when adding an external clause.
///
/// This is ignored for writing proof files but required for on-the-fly checking.
pub fn add_clause<'a>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP),
    clause: &[Lit],
) {
    if let Some(checker) = &mut ctx.part_mut(ProofP).checker {
        let result = checker.add_clause(clause);
        handle_self_check_result(ctx.borrow(), result);
    }
    if clause.len() > 1 {
        ctx.part_mut(ProofP).clause_count += 1;
    }
}

/// Add a step to the proof.
///
/// Ignored when proof generation is disabled.
pub fn add_step<'a, 's>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP),
    step: &'s ProofStep<'s>,
) {
    let proof = ctx.part_mut(ProofP);

    // This is a crude hack, as delete steps are the only ones emitted during loading. We need this
    // to avoid triggering a hash size adjustment during the initial load. The checker has already
    // loaded the complete formula, so our clause count doesn't match the checker's and we could
    // cause way too many collisions, causing the checker to have quadratic runtime.
    match step {
        ProofStep::DeleteClause { .. } => {}
        _ => proof.initial_load_complete = true,
    }

    let io_result = match proof.format {
        Some(ProofFormat::Varisat) => write_varisat_step(ctx.borrow(), step),
        Some(ProofFormat::Drat) => {
            let step = proof.map_step.map(step, |lit| lit, |hash| hash);
            drat::write_step(&mut proof.target, &step)
        }
        Some(ProofFormat::BinaryDrat) => {
            let step = proof.map_step.map(step, |lit| lit, |hash| hash);
            drat::write_binary_step(&mut proof.target, &step)
        }
        None => Ok(()),
    };

    if io_result.is_ok() {
        let proof = ctx.part_mut(ProofP);
        if let Some(checker) = &mut proof.checker {
            let step = proof.map_step.map(step, |lit| lit, |hash| hash);
            let result = checker.check_step(step);
            handle_self_check_result(ctx.borrow(), result);
        }
    }

    handle_io_errors(ctx.borrow(), io_result);
}

/// Write a step using our native format
fn write_varisat_step<'a, 's>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP),
    step: &'s ProofStep<'s>,
) -> io::Result<()> {
    let proof = ctx.part_mut(ProofP);

    proof.clause_count += step.clause_count_delta();

    let mut rehash = false;
    // Should we change the hash size?
    while proof.clause_count > (1 << (proof.hash_bits / 2)) {
        proof.hash_bits += 2;
        rehash = true;
    }
    if proof.initial_load_complete {
        while proof.hash_bits > 6 && proof.clause_count * 4 < (1 << (proof.hash_bits / 2)) {
            proof.hash_bits -= 2;
            rehash = true;
        }
    }

    if rehash {
        varisat::write_step(
            &mut proof.target,
            &ProofStep::ChangeHashBits(proof.hash_bits),
        )?;
    }

    let shift_bits = ClauseHash::max_value().count_ones() - proof.hash_bits;

    let map_hash = |hash| hash >> shift_bits;
    let step = proof.map_step.map(step, |lit| lit, map_hash);

    if proof.format == Some(ProofFormat::Varisat) {
        varisat::write_step(&mut proof.target, &step)?;
    }

    Ok(())
}

/// Flush buffers used for writing proof steps.
pub fn flush_proof<'a>(mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP)) {
    // We need to explicitly flush to handle IO errors.
    let result = ctx.part_mut(ProofP).target.flush();
    handle_io_errors(ctx.borrow(), result);
}

/// Stop writing proof steps.
pub fn close_proof<'a>(mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP)) {
    flush_proof(ctx.borrow());
    ctx.part_mut(ProofP).format = None;
    ctx.part_mut(ProofP).target = BufWriter::new(Box::new(sink()));
}

/// Called before solve returns to flush buffers and to trigger delayed unit conflict processing.
///
/// We flush buffers before solve returns to ensure that we can pass IO errors to the user.
pub fn solve_finished<'a>(mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP)) {
    flush_proof(ctx.borrow());
    if let Some(checker) = &mut ctx.part_mut(ProofP).checker {
        let result = checker.process_unit_conflicts();
        handle_self_check_result(ctx.borrow(), result);
    }
}

/// Handle results of on the fly checking.
///
/// Panics when the proof is incorrect and aborts solving when a proof processor produced an error.
fn handle_self_check_result<'a>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP),
    result: Result<(), CheckerError>,
) {
    match result {
        Err(CheckerError::ProofProcessorError { cause }) => {
            ctx.part_mut(SolverStateP).solver_error =
                Some(SolverError::ProofProcessorError { cause });
            *ctx.part_mut(ProofP) = Proof::default();
        }
        Err(err) => {
            log::error!("{}", err);
            if let CheckerError::CheckFailed { debug_step, .. } = err {
                if !debug_step.is_empty() {
                    log::error!("failed step was {}", debug_step)
                }
            }
            panic!("self check failure");
        }
        Ok(()) => (),
    }
}

/// Handle io errors during proof writing.
fn handle_io_errors<'a>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP),
    result: io::Result<()>,
) {
    if let Err(io_err) = result {
        ctx.part_mut(SolverStateP).solver_error = Some(SolverError::ProofIoError { cause: io_err });
        *ctx.part_mut(ProofP) = Proof::default();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;

    use std::fs::File;
    use std::process::Command;

    use failure::Fail;

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

            prop_assert_eq!(solver.solve().ok(), Some(false));

            solver.close_proof().map_err(|e| e.compat())?;

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

            prop_assert_eq!(solver.solve().ok(), Some(false));

            solver.close_proof().map_err(|e| e.compat())?;

            let output = Command::new("drat-trim")
                .arg(&cnf_file)
                .arg(&drat_proof)
                .arg("-i")
                .output()?;

            prop_assert!(std::str::from_utf8(&output.stdout)?.contains("s VERIFIED"));
        }
    }
}
