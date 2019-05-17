//! Unit propagation.
use partial_ref::{partial, PartialRef};

use crate::context::{parts::*, Context};

pub mod assignment;
pub mod binary;
pub mod graph;
pub mod long;
pub mod watch;

pub use assignment::{backtrack, enqueue_assignment, full_restart, restart, Assignment, Trail};
pub use graph::{Conflict, ImplGraph, ImplNode, Reason};
pub use watch::{enable_watchlists, Watch, Watchlists};

/// Propagate enqueued assignments.
///
/// Returns when all enqueued assignments are propagated, including newly propagated assignemnts, or
/// if there is a conflict.
///
/// On conflict the first propagation that would assign the opposite value to an already assigned
/// literal is returned.
pub fn propagate(
    mut ctx: partial!(
        Context,
        mut AssignmentP,
        mut ClauseAllocP,
        mut ImplGraphP,
        mut TrailP,
        mut WatchlistsP,
        BinaryClausesP,
        ClauseDbP,
    ),
) -> Result<(), Conflict> {
    enable_watchlists(ctx.borrow());

    while let Some(lit) = ctx.part_mut(TrailP).pop_queue() {
        binary::propagate_binary(ctx.borrow(), lit)?;
        long::propagate_long(ctx.borrow(), lit)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::cmp::max;

    use proptest::{prelude::*, *};

    use rand::distributions::Bernoulli;
    use rand::seq::SliceRandom;

    use partial_ref::IntoPartialRefMut;

    use varisat_formula::{cnf::strategy::*, CnfFormula, Lit};

    use crate::clause::{db, gc};
    use crate::context::{set_var_count, Context, SolverStateP};
    use crate::load::load_clause;
    use crate::state::SatState;

    /// Generate a random formula and list of implied literals.
    pub fn prop_formula(
        vars: impl Strategy<Value = usize>,
        extra_vars: impl Strategy<Value = usize>,
        extra_clauses: impl Strategy<Value = usize>,
        density: impl Strategy<Value = f64>,
    ) -> impl Strategy<Value = (Vec<Lit>, CnfFormula)> {
        (vars, extra_vars, extra_clauses, density).prop_flat_map(
            |(vars, extra_vars, extra_clauses, density)| {
                let negate = collection::vec(bool::ANY, vars + extra_vars);

                let dist = Bernoulli::new(density);

                let lits = negate
                    .prop_map(|negate| {
                        negate
                            .into_iter()
                            .enumerate()
                            .map(|(index, negate)| Lit::from_index(index, negate))
                            .collect::<Vec<_>>()
                    })
                    .prop_shuffle();

                lits.prop_perturb(move |mut lits, mut rng| {
                    let assigned_lits = &lits[..vars];

                    let mut clauses: Vec<Vec<Lit>> = vec![];
                    for (i, &lit) in assigned_lits.iter().enumerate() {
                        // Build a clause that implies lit
                        let mut clause = vec![lit];
                        for &reason_lit in assigned_lits[..i].iter() {
                            if rng.sample(dist) {
                                clause.push(!reason_lit);
                            }
                        }
                        clause.shuffle(&mut rng);
                        clauses.push(clause);
                    }

                    for _ in 0..extra_clauses {
                        // Build a clause that is satisfied
                        let &true_lit = assigned_lits.choose(&mut rng).unwrap();
                        let mut clause = vec![true_lit];
                        for &other_lit in lits.iter() {
                            if other_lit != true_lit && rng.sample(dist) {
                                clause.push(other_lit ^ rng.gen::<bool>());
                            }
                        }
                        clause.shuffle(&mut rng);
                        clauses.push(clause);
                    }

                    clauses.shuffle(&mut rng);

                    // Only return implied lits
                    lits.drain(vars..);

                    (lits, CnfFormula::from(clauses))
                })
            },
        )
    }

    proptest! {
        #[test]
        fn propagation_no_conflict(
            (mut lits, formula) in prop_formula(
                2..30usize,
                0..10usize,
                0..20usize,
                0.1..0.9
            ),
        ) {
            let mut ctx = Context::default();
            let mut ctx = ctx.into_partial_ref_mut();

            set_var_count(ctx.borrow(), formula.var_count());

            for clause in formula.iter() {
                load_clause(ctx.borrow(), clause);
            }

            prop_assert_eq!(ctx.part(SolverStateP).sat_state, SatState::Unknown);

            let prop_result = propagate(ctx.borrow());

            prop_assert_eq!(prop_result, Ok(()));

            lits.sort();

            let mut prop_lits = ctx.part(TrailP).trail().to_owned();

            prop_lits.sort();

            prop_assert_eq!(prop_lits, lits);
        }

        #[test]
        fn propagation_conflict(
            (lits, formula) in prop_formula(
                2..30usize,
                0..10usize,
                0..20usize,
                0.1..0.9
            ),
            conflict_size in any::<sample::Index>(),
        ) {
            let mut ctx = Context::default();
            let mut ctx = ctx.into_partial_ref_mut();

            set_var_count(ctx.borrow(), formula.var_count());

            // We add the conflict clause first to make sure that it isn't simplified during loading

            let conflict_size = conflict_size.index(lits.len() - 1) + 2;

            let conflict_clause: Vec<_> = lits[..conflict_size].iter().map(|&lit| !lit).collect();

            load_clause(ctx.borrow(), &conflict_clause);

            for clause in formula.iter() {
                load_clause(ctx.borrow(), clause);
            }

            prop_assert_eq!(ctx.part(SolverStateP).sat_state, SatState::Unknown);

            let prop_result = propagate(ctx.borrow());

            prop_assert!(prop_result.is_err());

            let conflict = prop_result.unwrap_err();

            let conflict_lits = conflict.lits(&ctx.borrow()).to_owned();

            for &lit in conflict_lits.iter() {
                prop_assert!(ctx.part(AssignmentP).lit_is_false(lit));
            }
        }

        #[test]
        fn propagation_no_conflict_after_gc(
            tmp_formula in cnf_formula(3..30usize, 30..100, 3..30),
            (mut lits, formula) in prop_formula(
                2..30usize,
                0..10usize,
                0..20usize,
                0.1..0.9
            ),
        ) {
            let mut ctx = Context::default();
            let mut ctx = ctx.into_partial_ref_mut();

            set_var_count(ctx.borrow(), max(tmp_formula.var_count(), formula.var_count()));

            for clause in tmp_formula.iter() {
                // Only add long clauses here
                let mut lits = clause.to_owned();
                lits.sort();
                lits.dedup();
                if lits.len() >= 3 {
                    load_clause(ctx.borrow(), clause);
                }
            }

            let tmp_crefs: Vec<_> = db::clauses_iter(&mut ctx.borrow()).collect();

            for clause in formula.iter() {
                load_clause(ctx.borrow(), clause);
            }

            for cref in tmp_crefs {
                db::delete_clause(ctx.borrow(), cref);
            }

            gc::collect_garbage(ctx.borrow());

            prop_assert_eq!(ctx.part(SolverStateP).sat_state, SatState::Unknown);

            let prop_result = propagate(ctx.borrow());

            prop_assert_eq!(prop_result, Ok(()));

            lits.sort();

            let mut prop_lits = ctx.part(TrailP).trail().to_owned();

            prop_lits.sort();

            prop_assert_eq!(prop_lits, lits);
        }
    }
}
