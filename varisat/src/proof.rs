//! Proof generation.

use std::io::{self, sink, BufWriter, Write};

use partial_ref::{partial, PartialRef};

use varisat_checker::{internal::SelfChecker, Checker, CheckerError, ProofProcessor};
use varisat_formula::{Lit, Var};
use varisat_internal_proof::{ClauseHash, ProofStep};

use crate::context::{parts::*, Context};
use crate::solver::SolverError;

mod drat;
mod map_step;

/// Proof formats that can be generated during solving.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum ProofFormat {
    Varisat,
    Drat,
    BinaryDrat,
}

/// Number of added or removed clauses.
pub fn clause_count_delta(step: &ProofStep) -> isize {
    match step {
        ProofStep::AddClause { clause } | ProofStep::AtClause { clause, .. } => {
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
        ProofStep::SolverVarName { .. }
        | ProofStep::UserVarName { .. }
        | ProofStep::UnitClauses(..)
        | ProofStep::ChangeHashBits(..)
        | ProofStep::Model(..)
        | ProofStep::Assumptions(..)
        | ProofStep::FailedAssumptions { .. }
        | ProofStep::End => 0,
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

    /// Are we emitting or checking our native format.
    pub fn native_format(&self) -> bool {
        self.checker.is_some()
            || match self.format {
                Some(ProofFormat::Varisat) => true,
                _ => false,
            }
    }

    /// Whether clause hashes are required for steps that support them.
    pub fn clause_hashes_required(&self) -> bool {
        self.native_format()
    }

    /// Whether unit clauses discovered through unit propagation have to be proven.
    pub fn prove_propagated_unit_clauses(&self) -> bool {
        self.native_format()
    }

    /// Whether found models are included in the proof.
    pub fn models_in_proof(&self) -> bool {
        self.native_format()
    }
}

/// Call when adding an external clause.
///
/// This is required for on the fly checking and checking of incremental solving.
///
/// *Note:* this function expects the clause to use solver var names.
pub fn add_clause<'a>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP, VariablesP),
    clause: &[Lit],
) {
    if ctx.part(SolverStateP).solver_invoked {
        add_step(ctx.borrow(), true, &ProofStep::AddClause { clause })
    } else {
        let (variables, mut ctx) = ctx.split_part(VariablesP);
        let proof = ctx.part_mut(ProofP);
        if let Some(checker) = &mut proof.checker {
            let clause = proof.map_step.map_lits(clause, |var| {
                variables
                    .global_from_solver()
                    .get(var)
                    .expect("no existing global var for solver var")
            });

            let result = checker.add_clause(clause);
            handle_self_check_result(ctx.borrow(), result);
        }
        if clause.len() > 1 {
            ctx.part_mut(ProofP).clause_count += 1;
        }
    }
}

/// Add a step to the proof.
///
/// Ignored when proof generation is disabled.
///
/// When `solver_vars` is true, all variables and literals will be converted from solver to global
/// vars. Otherwise the proof step needs to use global vars.
pub fn add_step<'a, 's>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP, VariablesP),
    solver_vars: bool,
    step: &'s ProofStep<'s>,
) {
    if ctx.part(SolverStateP).solver_error.is_some() {
        return;
    }

    if ctx.part(SolverStateP).solver_error.is_some() {
        return;
    }

    let (variables, mut ctx) = ctx.split_part(VariablesP);
    let proof = ctx.part_mut(ProofP);

    let map_vars = |var| {
        if solver_vars {
            variables
                .global_from_solver()
                .get(var)
                .expect("no existing global var for solver var")
        } else {
            var
        }
    };

    let io_result = match proof.format {
        Some(ProofFormat::Varisat) => write_varisat_step(ctx.borrow(), map_vars, step),
        Some(ProofFormat::Drat) => {
            let step = proof.map_step.map(step, map_vars, |hash| hash);
            drat::write_step(&mut proof.target, &step)
        }
        Some(ProofFormat::BinaryDrat) => {
            let step = proof.map_step.map(step, map_vars, |hash| hash);
            drat::write_binary_step(&mut proof.target, &step)
        }
        None => Ok(()),
    };

    if io_result.is_ok() {
        let proof = ctx.part_mut(ProofP);
        if let Some(checker) = &mut proof.checker {
            let step = proof.map_step.map(step, map_vars, |hash| hash);
            let result = checker.self_check_step(step);
            handle_self_check_result(ctx.borrow(), result);
        }
    }

    handle_io_errors(ctx.borrow(), io_result);
}

/// Write a step using our native format
fn write_varisat_step<'a, 's>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, SolverStateP),
    map_vars: impl Fn(Var) -> Var,
    step: &'s ProofStep<'s>,
) -> io::Result<()> {
    let (proof, ctx) = ctx.split_part_mut(ProofP);

    proof.clause_count += clause_count_delta(step);

    let mut rehash = false;
    // Should we change the hash size?
    while proof.clause_count > (1 << (proof.hash_bits / 2)) {
        proof.hash_bits += 2;
        rehash = true;
    }
    if ctx.part(SolverStateP).solver_invoked {
        while proof.hash_bits > 6 && proof.clause_count * 4 < (1 << (proof.hash_bits / 2)) {
            proof.hash_bits -= 2;
            rehash = true;
        }
    }

    if rehash {
        varisat_internal_proof::binary_format::write_step(
            &mut proof.target,
            &ProofStep::ChangeHashBits(proof.hash_bits),
        )?;
    }

    let shift_bits = ClauseHash::max_value().count_ones() - proof.hash_bits;

    let map_hash = |hash| hash >> shift_bits;
    let step = proof.map_step.map(step, map_vars, map_hash);

    if proof.format == Some(ProofFormat::Varisat) {
        varisat_internal_proof::binary_format::write_step(&mut proof.target, &step)?;
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
pub fn close_proof<'a>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP, VariablesP),
) {
    add_step(ctx.borrow(), true, &ProofStep::End);
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
        let result = checker.self_check_delayed_steps();
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

    use varisat_dimacs::write_dimacs;
    use varisat_formula::test::sgen_unsat_formula;

    use crate::solver::Solver;

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
