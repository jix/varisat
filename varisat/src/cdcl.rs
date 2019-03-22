//! Conflict driven clause learning.

use partial_ref::{partial, PartialRef};

use crate::analyze_conflict::analyze_conflict;
use crate::clause::{assess_learned_clause, bump_clause, db, decay_clause_activities};
use crate::context::{
    AnalyzeConflictP, AssignmentP, BinaryClausesP, ClauseActivityP, ClauseAllocP, ClauseDbP,
    Context, ImplGraphP, SolverStateP, TmpDataP, TrailP, VsidsP, WatchlistsP,
};
use crate::decision::make_decision;
use crate::prop::{backtrack, enqueue_assignment, propagate, Conflict, Reason};
use crate::simplify::simplify;
use crate::state::SatState;

/// Find a conflict, learn a clause and backtrack.
pub fn conflict_step(
    mut ctx: partial!(
        Context,
        mut AnalyzeConflictP,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ClauseActivityP,
        mut ClauseAllocP,
        mut ClauseDbP,
        mut ImplGraphP,
        mut SolverStateP,
        mut TmpDataP,
        mut TrailP,
        mut VsidsP,
        mut WatchlistsP,
    ),
) {
    let conflict = find_conflict(ctx.borrow());

    let conflict = match conflict {
        Ok(()) => {
            ctx.part_mut(SolverStateP).sat_state = SatState::Sat;
            return;
        }
        Err(conflict) => conflict,
    };

    let backtrack_to = analyze_conflict(ctx.borrow(), conflict);

    let (analyze, mut ctx) = ctx.split_part(AnalyzeConflictP);

    for &cref in analyze.involved() {
        bump_clause(ctx.borrow(), cref);
    }

    decay_clause_activities(ctx.borrow());

    // TODO Handle incremental solving

    backtrack(ctx.borrow(), backtrack_to);

    let clause = analyze.clause();

    let reason = match clause.len() {
        0 => {
            ctx.part_mut(SolverStateP).sat_state = SatState::Unsat;
            return;
        }
        1 => Reason::Unit,
        2 => {
            ctx.part_mut(BinaryClausesP)
                .add_binary_clause([clause[0], clause[1]]);
            Reason::Binary([clause[1]])
        }
        _ => {
            let header = assess_learned_clause(ctx.borrow(), clause);
            let cref = db::add_clause(ctx.borrow(), header, clause);
            Reason::Long(cref)
        }
    };

    enqueue_assignment(ctx.borrow(), clause[0], reason);
}

/// Find a conflict.
///
/// Returns `Err` if a conflict was found and `Ok` if a satisfying assignment was found instead.
pub fn find_conflict(
    mut ctx: partial!(
        Context,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ClauseAllocP,
        mut ClauseDbP,
        mut ImplGraphP,
        mut TrailP,
        mut VsidsP,
        mut WatchlistsP,
    ),
) -> Result<(), Conflict> {
    loop {
        propagate(ctx.borrow())?;

        if ctx.part(TrailP).current_level() == 0 {
            if !ctx.part(TrailP).trail().is_empty() {
                simplify(ctx.borrow());
            }
        }

        // TODO Handle incremental solving

        if !make_decision(ctx.borrow()) {
            return Ok(());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;

    use partial_ref::IntoPartialRefMut;

    use crate::context::{set_var_count, AssignmentP, SolverStateP};
    use crate::load::load_clause;
    use crate::state::SatState;

    use crate::test::{sat_formula, sgen_unsat_formula};

    #[test]
    fn level_0_unsat() {
        let mut ctx = Context::default();
        let mut ctx = ctx.into_partial_ref_mut();

        let formula = cnf_formula![
            1, 2, 3;
            -1;
            1, -2;
            2, -3;
        ];

        set_var_count(ctx.borrow(), formula.var_count());

        for clause in formula.iter() {
            load_clause(ctx.borrow(), clause);
        }

        while ctx.part(SolverStateP).sat_state == SatState::Unknown {
            conflict_step(ctx.borrow());
        }

        assert_eq!(ctx.part(SolverStateP).sat_state, SatState::Unsat);
    }

    proptest! {
        #[test]
        fn sgen_unsat(formula in sgen_unsat_formula(1..7usize)) {
            let mut ctx = Context::default();
            let mut ctx = ctx.into_partial_ref_mut();

            set_var_count(ctx.borrow(), formula.var_count());

            for clause in formula.iter() {
                load_clause(ctx.borrow(), clause);
            }

            while ctx.part(SolverStateP).sat_state == SatState::Unknown {
                conflict_step(ctx.borrow());
            }

            prop_assert_eq!(ctx.part(SolverStateP).sat_state, SatState::Unsat);
        }

        #[test]
        fn sat(formula in sat_formula(4..20usize, 10..100usize, 0.05..0.2, 0.9..1.0)) {
            let mut ctx = Context::default();
            let mut ctx = ctx.into_partial_ref_mut();

            set_var_count(ctx.borrow(), formula.var_count());

            for clause in formula.iter() {
                load_clause(ctx.borrow(), clause);
            }

            while ctx.part(SolverStateP).sat_state == SatState::Unknown {
                conflict_step(ctx.borrow());
            }

            prop_assert_eq!(ctx.part(SolverStateP).sat_state, SatState::Sat);

            for clause in formula.iter() {
                prop_assert!(clause.iter().any(|&lit| ctx.part(AssignmentP).lit_is_true(lit)));
            }
        }

        #[test]
        fn sgen_unsat_incremetal_clauses(formula in sgen_unsat_formula(1..7usize)) {
            let mut ctx = Context::default();
            let mut ctx = ctx.into_partial_ref_mut();

            set_var_count(ctx.borrow(), formula.var_count());

            let mut last_state = SatState::Sat;

            for clause in formula.iter() {
                load_clause(ctx.borrow(), clause);
                while ctx.part(SolverStateP).sat_state == SatState::Unknown {
                    conflict_step(ctx.borrow());
                }

                if ctx.part(SolverStateP).sat_state != last_state {
                    prop_assert_eq!(ctx.part(SolverStateP).sat_state, SatState::Unsat);
                    prop_assert_eq!(last_state, SatState::Sat);
                    last_state = ctx.part(SolverStateP).sat_state;
                }
            }

            prop_assert_eq!(last_state, SatState::Unsat);
        }
    }
}
