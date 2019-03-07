//! Boolean satisfiability solver.
use std::io;

use partial_ref::{IntoPartialRef, IntoPartialRefMut, PartialRef};

use failure::Error;
use log::info;

use crate::cdcl::conflict_step;
use crate::cnf::CnfFormula;
use crate::context::{ensure_var_count, AssignmentP, Context, SolverStateP};
use crate::dimacs::{DimacsHeader, DimacsParser};
use crate::lit::{Lit, Var};
use crate::load::load_clause;
use crate::state::SatState;

/// A boolean satisfiability solver.
#[derive(Default)]
pub struct Solver {
    ctx: Box<Context>,
}

impl Solver {
    /// Create a new solver.
    pub fn new() -> Solver {
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
        while ctx.part(SolverStateP).sat_state == SatState::Unknown {
            conflict_step(ctx.borrow());
        }
        match ctx.part(SolverStateP).sat_state {
            SatState::Unknown => None,
            SatState::Sat => Some(true),
            SatState::Unsat | SatState::UnsatUnderAssumptions => Some(false),
        }
    }

    /// Set of literals that satisfy the formula.
    pub fn model(&self) -> Option<Vec<Lit>> {
        let mut ctx = self.ctx.into_partial_ref();
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
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;

    use crate::cnf::CnfFormula;
    use crate::dimacs::write_dimacs;

    use crate::test::{sat_formula, sgen_unsat_formula};

    proptest! {
        #[test]
        fn sgen_unsat(formula in sgen_unsat_formula(1..7usize)) {
            let mut solver = Solver::new();

            solver.add_formula(&formula);

            prop_assert_eq!(solver.solve(), Some(false));
        }

        #[test]
        fn sat(formula in sat_formula(4..20usize, 10..100usize, 0.05..0.2, 0.9..1.0)) {
            let mut solver = Solver::new();

            solver.add_formula(&formula);

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
    }

}
