//! Boolean satisfiability solver.
use std::io;

use partial_ref::{IntoPartialRef, IntoPartialRefMut, PartialRef};

use failure::{Error, Fail};

use crate::checker::ProofProcessor;
use crate::cnf::CnfFormula;
use crate::config::SolverConfigUpdate;
use crate::context::{config_changed, ensure_var_count, AssignmentP, Context, SolverStateP};
use crate::dimacs::DimacsParser;
use crate::incremental::set_assumptions;
use crate::lit::Lit;
use crate::load::load_clause;
use crate::proof;
use crate::schedule::schedule_step;
use crate::state::SatState;

pub use crate::proof::ProofFormat;

/// Possible errors while solving a formula.
#[derive(Debug, Fail)]
pub enum SolverError {
    #[fail(display = "The solver was interrupted")]
    Interrupted,
    #[fail(display = "Error in proof processor: {}", cause)]
    ProofProcessorError {
        #[cause]
        cause: Error,
    },
    #[fail(display = "Error writing proof file: {}", cause)]
    ProofIoError {
        #[cause]
        cause: io::Error,
    },
    #[doc(hidden)]
    #[fail(display = "__Nonexhaustive")]
    __Nonexhaustive,
}

impl SolverError {
    /// Whether a Solver instance can be used after producing such an error.
    pub fn is_recoverable(&self) -> bool {
        match self {
            SolverError::Interrupted => true,
            _ => false,
        }
    }
}

/// A boolean satisfiability solver.
#[derive(Default)]
pub struct Solver<'a> {
    ctx: Box<Context<'a>>,
}

impl<'a> Solver<'a> {
    /// Create a new solver.
    pub fn new() -> Solver<'a> {
        Solver::default()
    }

    /// Change the solver configuration.
    pub fn config(&mut self, config_update: &SolverConfigUpdate) -> Result<(), Error> {
        config_update.apply(&mut self.ctx.solver_config)?;
        let mut ctx = self.ctx.into_partial_ref_mut();
        config_changed(ctx.borrow(), config_update);
        Ok(())
    }

    /// Add a formula to the solver.
    pub fn add_formula(&mut self, formula: &CnfFormula) {
        let mut ctx = self.ctx.into_partial_ref_mut();
        ensure_var_count(ctx.borrow(), formula.var_count());
        for clause in formula.iter() {
            load_clause(ctx.borrow(), clause);
        }
    }

    /// Add a clause to the solver.
    pub fn add_clause(&mut self, clause: &[Lit]) {
        self.ensure_var_count_from_slice(clause);
        let mut ctx = self.ctx.into_partial_ref_mut();
        load_clause(ctx.borrow(), clause);
    }

    /// Increases the variable count to handle all literals in the given slice.
    fn ensure_var_count_from_slice(&mut self, lits: &[Lit]) {
        if let Some(index) = lits.iter().map(|&lit| lit.index()).max() {
            let mut ctx = self.ctx.into_partial_ref_mut();
            ensure_var_count(ctx.borrow(), index + 1);
        }
    }

    /// Reads and adds a formula in DIMACS CNF format.
    ///
    /// Using this avoids creating a temporary [`CnfFormula`].
    pub fn add_dimacs_cnf(&mut self, input: impl io::Read) -> Result<(), Error> {
        let parser = DimacsParser::parse_incremental(input, |parser| {
            Ok(self.add_formula(&parser.take_formula()))
        })?;

        log::info!(
            "Parsed formula with {} variables and {} clauses",
            parser.var_count(),
            parser.clause_count()
        );

        Ok(())
    }

    /// Check the satisfiability of the current formula.
    pub fn solve(&mut self) -> Result<bool, SolverError> {
        let mut ctx = self.ctx.into_partial_ref_mut();
        assert!(
            !ctx.part_mut(SolverStateP).state_is_invalid,
            "solve() called after encountering an unrecoverable error"
        );

        while schedule_step(ctx.borrow()) {}

        proof::solve_finished(ctx.borrow());

        self.check_for_solver_error()?;

        match self.ctx.solver_state.sat_state {
            SatState::Unknown => Err(SolverError::Interrupted),
            SatState::Sat => Ok(true),
            SatState::Unsat | SatState::UnsatUnderAssumptions => Ok(false),
        }
    }

    /// Check for asynchronously generated errors.
    ///
    /// To avoid threading errors out of deep call stacks, we have a solver_error field in the
    /// SolverState. This function takes and returns that error if present.
    fn check_for_solver_error(&mut self) -> Result<(), SolverError> {
        let mut ctx = self.ctx.into_partial_ref_mut();
        let error = ctx.part_mut(SolverStateP).solver_error.take();

        if let Some(error) = error {
            if !error.is_recoverable() {
                ctx.part_mut(SolverStateP).state_is_invalid = true;
            }
            Err(error)
        } else {
            Ok(())
        }
    }

    /// Assume given literals for future calls to solve.
    ///
    /// This replaces the current set of assumed literals.
    pub fn assume(&mut self, assumptions: &[Lit]) {
        self.ensure_var_count_from_slice(assumptions);
        let mut ctx = self.ctx.into_partial_ref_mut();
        set_assumptions(ctx.borrow(), assumptions);
    }

    /// Set of literals that satisfy the formula.
    pub fn model(&self) -> Option<Vec<Lit>> {
        let ctx = self.ctx.into_partial_ref();
        if ctx.part(SolverStateP).sat_state == SatState::Sat {
            Some(
                ctx.part(AssignmentP)
                    .assignment()
                    .iter()
                    .enumerate()
                    .flat_map(|(index, assignment)| {
                        assignment.map(|polarity| Lit::from_index(index, !polarity))
                    })
                    .collect(),
            )
        } else {
            None
        }
    }

    /// Subset of the assumptions that made the formula unsatisfiable.
    ///
    /// This is not guaranteed to be minimal and may just return all assumptions every time.
    pub fn failed_core(&self) -> Option<&[Lit]> {
        match self.ctx.solver_state.sat_state {
            SatState::UnsatUnderAssumptions => Some(self.ctx.incremental.failed_core()),
            SatState::Unsat => Some(&[]),
            SatState::Unknown | SatState::Sat => None,
        }
    }

    /// Generate a proof of unsatisfiability during solving.
    ///
    /// This needs to be called before any clauses are added.
    pub fn write_proof(&mut self, target: impl io::Write + 'a, format: ProofFormat) {
        assert!(
            self.ctx.solver_state.formula_is_empty,
            "called after clauses were added"
        );
        self.ctx.proof.write_proof(target, format);
    }

    /// Stop generating a proof of unsatisfiability.
    ///
    /// This also flushes internal buffers and closes the target file.
    pub fn close_proof(&mut self) -> Result<(), SolverError> {
        let mut ctx = self.ctx.into_partial_ref_mut();
        proof::close_proof(ctx.borrow());
        self.check_for_solver_error()
    }

    /// Generate and check a proof on the fly.
    ///
    /// This needs to be called before any clauses are added.
    pub fn enable_self_checking(&mut self) {
        assert!(
            self.ctx.solver_state.formula_is_empty,
            "called after clauses were added"
        );
        self.ctx.proof.begin_checking();
    }

    /// Generate a proof and process it using a [`ProofProcessor`].
    ///
    /// This implicitly enables self checking.
    ///
    /// This needs to be called before any clauses are added.
    pub fn add_proof_processor(&mut self, processor: &'a mut dyn ProofProcessor) {
        assert!(
            self.ctx.solver_state.formula_is_empty,
            "called after clauses were added"
        );
        self.ctx.proof.add_processor(processor);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;

    use crate::checker::CheckedProofStep;
    use crate::cnf::CnfFormula;
    use crate::dimacs::write_dimacs;
    use crate::lit::Var;

    use crate::test::{conditional_pigeon_hole, sat_formula, sgen_unsat_formula};

    fn enable_test_schedule(solver: &mut Solver) {
        let mut config = SolverConfigUpdate::new();
        config.reduce_locals_interval = Some(150);
        config.reduce_mids_interval = Some(100);

        solver.config(&config).unwrap();
    }

    #[test]
    #[should_panic(expected = "solve() called after encountering an unrecoverable error")]
    fn error_handling_proof_writing() {
        let mut output_buffer = [0u8; 4];
        let mut solver = Solver::new();
        let proof_output = std::io::Cursor::new(&mut output_buffer[..]);

        solver.write_proof(proof_output, ProofFormat::Varisat);

        solver.add_formula(&cnf_formula![
            -1, -2, -3; -1, -2, -4; -1, -2, -5; -1, -3, -4; -1, -3, -5; -1, -4, -5; -2, -3, -4;
            -2, -3, -5; -2, -4, -5; -3, -4, -5; 1, 2, 5; 1, 2, 3; 1, 2, 4; 1, 5, 3; 1, 5, 4;
            1, 3, 4; 2, 5, 3; 2, 5, 4; 2, 3, 4; 5, 3, 4;
        ]);

        let result = solver.solve();

        assert!(match result {
            Err(SolverError::ProofIoError { .. }) => true,
            _ => false,
        });

        let _ = solver.solve();
    }

    struct FailingProcessor;

    impl ProofProcessor for FailingProcessor {
        fn process_step(&mut self, _step: &CheckedProofStep) -> Result<(), Error> {
            failure::bail!("failing processor");
        }
    }
    #[test]
    #[should_panic(expected = "solve() called after encountering an unrecoverable error")]
    fn error_handling_proof_processing() {
        let mut processor = FailingProcessor;

        let mut solver = Solver::new();

        solver.add_proof_processor(&mut processor);

        solver.add_formula(&cnf_formula![
            -1, -2, -3; -1, -2, -4; -1, -2, -5; -1, -3, -4; -1, -3, -5; -1, -4, -5; -2, -3, -4;
            -2, -3, -5; -2, -4, -5; -3, -4, -5; 1, 2, 5; 1, 2, 3; 1, 2, 4; 1, 5, 3; 1, 5, 4;
            1, 3, 4; 2, 5, 3; 2, 5, 4; 2, 3, 4; 5, 3, 4;
        ]);

        let result = solver.solve();

        assert!(match result {
            Err(SolverError::ProofProcessorError { cause }) => {
                format!("{}", cause) == "failing processor"
            }
            _ => false,
        });

        let _ = solver.solve();
    }

    #[test]
    #[should_panic(expected = "called after clauses were added")]
    fn write_proof_too_late() {
        let mut solver = Solver::new();
        solver.add_clause(&lits![1, 2, 3]);
        solver.write_proof(std::io::sink(), ProofFormat::Varisat);
    }

    #[test]
    #[should_panic(expected = "called after clauses were added")]
    fn add_proof_processor_too_late() {
        let mut processor = FailingProcessor;

        let mut solver = Solver::new();
        solver.add_clause(&lits![1, 2, 3]);

        solver.add_proof_processor(&mut processor);
    }

    #[test]
    #[should_panic(expected = "called after clauses were added")]
    fn enable_self_checking_too_late() {
        let mut solver = Solver::new();
        solver.add_clause(&lits![1, 2, 3]);

        solver.enable_self_checking();
    }

    #[test]
    fn self_check_duplicated_unit_clauses() {
        let mut solver = Solver::new();

        solver.enable_self_checking();

        solver.add_formula(&cnf_formula![
            4;
            4;
        ]);

        assert_eq!(solver.solve().ok(), Some(true));
    }

    proptest! {
        #[test]
        fn sgen_unsat(
            formula in sgen_unsat_formula(1..7usize),
            test_schedule in proptest::bool::ANY,
        ) {
            let mut solver = Solver::new();

            solver.add_formula(&formula);

            if test_schedule {
                enable_test_schedule(&mut solver);
            }

            prop_assert_eq!(solver.solve().ok(), Some(false));
        }

        #[test]
        fn sgen_unsat_checked(
            formula in sgen_unsat_formula(1..7usize),
            test_schedule in proptest::bool::ANY,
        ) {
            let mut solver = Solver::new();

            solver.enable_self_checking();

            solver.add_formula(&formula);

            if test_schedule {
                enable_test_schedule(&mut solver);
            }

            prop_assert_eq!(solver.solve().ok(), Some(false));
        }

        #[test]
        fn sat(
            formula in sat_formula(4..20usize, 10..100usize, 0.05..0.2, 0.9..1.0),
            test_schedule in proptest::bool::ANY,
        ) {
            let mut solver = Solver::new();

            solver.add_formula(&formula);

            if test_schedule {
                enable_test_schedule(&mut solver);
            }

            prop_assert_eq!(solver.solve().ok(), Some(true));

            let model = solver.model().unwrap();

            for clause in formula.iter() {
                prop_assert!(clause.iter().any(|lit| model.contains(lit)));
            }
        }

        #[test]
        fn sat_via_dimacs(formula in sat_formula(4..20usize, 10..100usize, 0.05..0.2, 0.9..1.0)) {
            let mut solver = Solver::new();

            let mut dimacs = vec![];

            write_dimacs(&mut dimacs, &formula).unwrap();

            solver.add_dimacs_cnf(&mut &dimacs[..]).unwrap();

            prop_assert_eq!(solver.solve().ok(), Some(true));

            let model = solver.model().unwrap();

            for clause in formula.iter() {
                prop_assert!(clause.iter().any(|lit| model.contains(lit)));
            }
        }

        #[test]
        fn sgen_unsat_incremental_clauses(formula in sgen_unsat_formula(1..7usize)) {
            let mut solver = Solver::new();

            let mut last_state = Some(true);

            for clause in formula.iter() {
                solver.add_clause(clause);

                let state = solver.solve().ok();
                if state != last_state {
                    prop_assert_eq!(state, Some(false));
                    prop_assert_eq!(last_state, Some(true));
                    last_state = state;
                }
            }

            prop_assert_eq!(last_state, Some(false));
        }

        #[test]
        fn pigeon_hole_unsat_assumption_core(
            (enable_row, columns, formula) in conditional_pigeon_hole(1..5usize, 1..5usize),
        ) {
            let mut solver = Solver::new();
            solver.add_formula(&formula);

            prop_assert_eq!(solver.solve().ok(), Some(true));

            let mut assumptions = enable_row.to_owned();

            assumptions.push(Lit::positive(Var::from_index(formula.var_count() + 10)));

            solver.assume(&assumptions);

            prop_assert_eq!(solver.solve().ok(), Some(false));


            let mut candidates = solver.failed_core().unwrap().to_owned();
            let mut core: Vec<Lit> = vec![];

            while !candidates.is_empty() {

                solver.assume(&candidates[0..candidates.len() - 1]);

                match solver.solve() {
                    Err(_) => unreachable!(),
                    Ok(true) => {
                        let skipped = *candidates.last().unwrap();
                        core.push(skipped);

                        let single_clause = CnfFormula::from(Some(&[skipped]));
                        solver.add_formula(&single_clause);
                    },
                    Ok(false) => {
                        candidates = solver.failed_core().unwrap().to_owned();
                    }
                }
            }

            prop_assert_eq!(core.len(), columns + 1);
        }
    }

}
