//! Boolean satisfiability solver.
use std::io;

use partial_ref::{IntoPartialRef, IntoPartialRefMut, PartialRef};

use failure::Error;
use log::info;

use crate::cnf::CnfFormula;
use crate::context::{ensure_var_count, AssignmentP, Context, SolverStateP};
use crate::dimacs::DimacsParser;
use crate::incremental::set_assumptions;
use crate::lit::{Lit, Var};
use crate::load::load_clause;
use crate::schedule::schedule_step;
use crate::state::SatState;

pub use crate::proof::ProofFormat;

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

    /// Add a formula to the solver.
    pub fn add_formula(&mut self, formula: &CnfFormula) {
        let mut ctx = self.ctx.into_partial_ref_mut();
        ensure_var_count(ctx.borrow(), formula.var_count());
        for clause in formula.iter() {
            load_clause(ctx.borrow(), clause);
        }
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

        info!(
            "Parsed formula with {} variables and {} clauses",
            parser.var_count(),
            parser.clause_count()
        );

        Ok(())
    }

    /// Check the satisfiability of the current formula.
    pub fn solve(&mut self) -> Option<bool> {
        let mut ctx = self.ctx.into_partial_ref_mut();

        while schedule_step(ctx.borrow()) {}

        match ctx.part(SolverStateP).sat_state {
            SatState::Unknown => None,
            SatState::Sat => Some(true),
            SatState::Unsat | SatState::UnsatUnderAssumptions => Some(false),
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
                        assignment.map(|polarity| Lit::from_var(Var::from_index(index), !polarity))
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
    pub fn write_proof(&mut self, target: impl io::Write + 'a, format: ProofFormat) {
        self.ctx.proof.write_proof(target, format);
    }

    /// Stop generating a proof of unsatisfiability.
    ///
    /// This also flushes internal buffers and closes the target file.
    pub fn close_proof(&mut self) {
        self.ctx.proof.close_proof();
    }

    /// Enables a test schedule that triggers steps early
    #[cfg(test)]
    fn enable_test_schedule(&mut self) {
        use crate::context::ScheduleP;
        self.ctx
            .into_partial_ref_mut()
            .part_mut(ScheduleP)
            .test_schedule = true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;

    use crate::cnf::CnfFormula;
    use crate::dimacs::write_dimacs;

    use crate::test::{conditional_pigeon_hole, sat_formula, sgen_unsat_formula};

    proptest! {
        #[test]
        fn sgen_unsat(
            formula in sgen_unsat_formula(1..7usize),
            test_schedule in proptest::bool::ANY,
        ) {
            let mut solver = Solver::new();

            solver.add_formula(&formula);

            if test_schedule {
                solver.enable_test_schedule();
            }

            prop_assert_eq!(solver.solve(), Some(false));
        }

        #[test]
        fn sat(
            formula in sat_formula(4..20usize, 10..100usize, 0.05..0.2, 0.9..1.0),
            test_schedule in proptest::bool::ANY,
        ) {
            let mut solver = Solver::new();

            solver.add_formula(&formula);

            if test_schedule {
                solver.enable_test_schedule();
            }

            prop_assert_eq!(solver.solve(), Some(true));

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

            prop_assert_eq!(solver.solve(), Some(true));

            let model = solver.model().unwrap();

            for clause in formula.iter() {
                prop_assert!(clause.iter().any(|lit| model.contains(lit)));
            }
        }

        #[test]
        fn sgen_unsat_incremetal_clauses(formula in sgen_unsat_formula(1..7usize)) {
            let mut solver = Solver::new();

            let mut last_state = Some(true);

            for clause in formula.iter() {
                let single_clause = CnfFormula::from(Some(clause));
                solver.add_formula(&single_clause);

                let state = solver.solve();
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

            prop_assert_eq!(solver.solve(), Some(true));

            let mut assumptions = enable_row.to_owned();

            assumptions.push(Lit::from_var(Var::from_index(formula.var_count() + 10), false));

            solver.assume(&assumptions);

            prop_assert_eq!(solver.solve(), Some(false));


            let mut candidates = solver.failed_core().unwrap().to_owned();
            let mut core: Vec<Lit> = vec![];

            while !candidates.is_empty() {

                solver.assume(&candidates[0..candidates.len() - 1]);

                match solver.solve() {
                    None => unreachable!(),
                    Some(true) => {
                        let skipped = *candidates.last().unwrap();
                        core.push(skipped);

                        let single_clause = CnfFormula::from(Some(&[skipped]));
                        solver.add_formula(&single_clause);
                    },
                    Some(false) => {
                        candidates = solver.failed_core().unwrap().to_owned();
                    }
                }
            }

            prop_assert_eq!(core.len(), columns + 1);
        }
    }

}
