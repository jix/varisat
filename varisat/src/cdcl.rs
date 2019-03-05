//! Conflict driven clause learning.

use partial_ref::{partial, PartialRef};

use crate::analyze_conflict::analyze_conflict;
use crate::clause::{db, ClauseHeader, Tier};
use crate::context::{
    AnalyzeConflictP, AssignmentP, BinaryClausesP, ClauseAllocP, ClauseDbP, Context, ImplGraphP,
    SolverStateP, TrailP, WatchlistsP,
};
use crate::decision::make_decision;
use crate::prop::{backtrack, enqueue_assignment, propagate, Conflict, Reason};
use crate::state::SatState;

/// Find a conflict, learn a clause and backtrack.
pub fn conflict_step(
    mut ctx: partial!(
        Context,
        mut AnalyzeConflictP,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ClauseAllocP,
        mut ClauseDbP,
        mut ImplGraphP,
        mut SolverStateP,
        mut TrailP,
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

    // TODO Handle incremental solving

    backtrack(ctx.borrow(), backtrack_to);

    let clause = ctx.part(AnalyzeConflictP).clause();

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
            let mut header = ClauseHeader::new();

            // TODO clause assessment
            header.set_tier(Tier::Local);

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
        mut ClauseAllocP,
        mut ImplGraphP,
        mut TrailP,
        mut WatchlistsP,
        BinaryClausesP,
        ClauseDbP,
    ),
) -> Result<(), Conflict> {
    loop {
        propagate(ctx.borrow())?;

        // TODO Handle incremental solving

        if !make_decision(ctx.borrow()) {
            return Ok(());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::{prelude::*, *};

    use rand::distributions::Bernoulli;
    use rand::seq::SliceRandom;

    use partial_ref::IntoPartialRefMut;

    use crate::cnf::CnfFormula;
    use crate::context::{set_var_count, AssignmentP, SolverStateP};
    use crate::lit::{Lit, Var};
    use crate::load::load_clause;
    use crate::state::SatState;

    /// Generate small hard unsat instances.
    ///
    /// Implementation of http://www.cs.qub.ac.uk/~i.spence/sgen/ but with random partitions
    pub fn sgen_unsat_formula(
        blocks: impl Strategy<Value = usize>,
    ) -> impl Strategy<Value = CnfFormula> {
        blocks.prop_flat_map(|blocks| {
            collection::vec(bool::ANY, blocks * 4 + 1).prop_perturb(|negate, mut rng| {
                let mut clauses: Vec<Vec<Lit>> = vec![];
                let mut lits = negate
                    .into_iter()
                    .enumerate()
                    .map(|(index, negate)| Lit::from_var(Var::from_index(index), negate))
                    .collect::<Vec<_>>();

                for &invert in [false, true].iter() {
                    lits.shuffle(&mut rng);
                    for block in lits.chunks_exact(4) {
                        for a in 0..4 {
                            for b in 0..a {
                                for c in 0..b {
                                    let mut clause = vec![
                                        block[a] ^ invert,
                                        block[b] ^ invert,
                                        block[c] ^ invert,
                                    ];
                                    clause.shuffle(&mut rng);
                                    clauses.push(clause);
                                }
                            }
                        }
                    }
                    let &lit_a = lits.last().unwrap();
                    for b in 0..4 {
                        for c in 0..b {
                            let mut clause =
                                vec![lit_a ^ invert, lits[b] ^ invert, lits[c] ^ invert];
                            clause.shuffle(&mut rng);
                            clauses.push(clause);
                        }
                    }
                }

                clauses.shuffle(&mut rng);
                CnfFormula::from(clauses)
            })
        })
    }

    /// Generate a sat instance.
    ///
    /// This generates a random full assignment and then only generates clauses compatible with that
    /// assignment.
    pub fn sat_formula(
        vars: impl Strategy<Value = usize>,
        clause_count: impl Strategy<Value = usize>,
        density: impl Strategy<Value = f64>,
        polarity_dist: impl Strategy<Value = f64>,
    ) -> impl Strategy<Value = CnfFormula> {
        (vars, clause_count, density, polarity_dist).prop_flat_map(
            |(vars, clause_count, density, polarity_dist)| {
                let density = Bernoulli::new(density);
                let polarity_dist = Bernoulli::new(polarity_dist);

                collection::vec(bool::ANY, vars).prop_perturb(move |negate, mut rng| {
                    let mut clauses: Vec<Vec<Lit>> = vec![];
                    let lits = negate
                        .into_iter()
                        .enumerate()
                        .map(|(index, negate)| Lit::from_var(Var::from_index(index), negate))
                        .collect::<Vec<_>>();

                    for _ in 0..clause_count {
                        let &fixed_lit = lits.choose(&mut rng).unwrap();
                        let mut clause = vec![fixed_lit];
                        for &lit in lits.iter() {
                            if lit != fixed_lit && rng.sample(density) {
                                clause.push(lit ^ rng.sample(polarity_dist));
                            }
                        }
                        clause.shuffle(&mut rng);
                        clauses.push(clause);
                    }

                    clauses.shuffle(&mut rng);
                    CnfFormula::from(clauses)
                })
            },
        )
    }

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
    }
}
