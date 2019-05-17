//! Incremental solving.

use partial_ref::{partial, PartialRef};

use varisat_formula::Lit;
use varisat_internal_proof::{clause_hash, lit_hash, ClauseHash, ProofStep};

use crate::context::{
    AssignmentP, ClauseAllocP, Context, ImplGraphP, IncrementalP, ProofP, SolverStateP, TmpDataP,
    TrailP, VsidsP,
};
use crate::proof;
use crate::prop::{enqueue_assignment, full_restart, Reason};
use crate::state::SatState;

/// Incremental solving.
#[derive(Default)]
pub struct Incremental {
    assumptions: Vec<Lit>,
    failed_core: Vec<Lit>,
    assumption_levels: usize,
    failed_propagation_hashes: Vec<ClauseHash>,
}

impl Incremental {
    /// Current number of decision levels used for assumptions.
    pub fn assumption_levels(&self) -> usize {
        self.assumption_levels
    }

    /// Resets assumption_levels to zero on a full restart.
    pub fn full_restart(&mut self) {
        self.assumption_levels = 0;
    }

    /// Subset of assumptions that made the formula unsatisfiable.
    pub fn failed_core(&self) -> &[Lit] {
        &self.failed_core
    }
}

/// Return type of [`enqueue_assumption`].
pub enum EnqueueAssumption {
    Done,
    Enqueued,
    Conflict,
}

/// Change the currently active assumptions.
pub fn set_assumptions<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut AssignmentP,
        mut IncrementalP,
        mut SolverStateP,
        mut TrailP,
        mut ProofP<'a>,
        mut VsidsP,
    ),
    assumptions: &[Lit],
) {
    full_restart(ctx.borrow());

    let state = ctx.part_mut(SolverStateP);

    state.sat_state = match state.sat_state {
        SatState::Unsat => SatState::Unsat,
        SatState::Sat | SatState::UnsatUnderAssumptions | SatState::Unknown => SatState::Unknown,
    };

    let incremental = ctx.part_mut(IncrementalP);

    incremental.assumptions.clear();
    incremental.assumptions.extend_from_slice(assumptions);

    proof::add_step(ctx.borrow(), &ProofStep::Assumptions(assumptions));
}

/// Enqueue another assumption if possible.
///
/// Returns whether an assumption was enqueued, whether no assumptions are left or whether the
/// assumptions result in a conflict.
pub fn enqueue_assumption<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut AssignmentP,
        mut ImplGraphP,
        mut IncrementalP,
        mut ProofP<'a>,
        mut SolverStateP,
        mut TmpDataP,
        mut TrailP,
        ClauseAllocP,
    ),
) -> EnqueueAssumption {
    while let Some(&assumption) = ctx
        .part(IncrementalP)
        .assumptions
        .get(ctx.part(TrailP).current_level())
    {
        match ctx.part(AssignmentP).lit_value(assumption) {
            Some(false) => {
                analyze_assumption_conflict(ctx.borrow(), assumption);
                return EnqueueAssumption::Conflict;
            }
            Some(true) => {
                // The next assumption is already implied by other assumptions so we can remove it.
                let level = ctx.part(TrailP).current_level();
                let incremental = ctx.part_mut(IncrementalP);
                incremental.assumptions.swap_remove(level);
            }
            None => {
                ctx.part_mut(TrailP).new_decision_level();
                enqueue_assignment(ctx.borrow(), assumption, Reason::Unit);
                let (incremental, ctx) = ctx.split_part_mut(IncrementalP);
                incremental.assumption_levels = ctx.part(TrailP).current_level();
                return EnqueueAssumption::Enqueued;
            }
        }
    }
    EnqueueAssumption::Done
}

/// Analyze a conflicting set of assumptions.
///
/// Compute a set of incompatible assumptions given an assumption that is incompatible with the
/// assumptions enqueued so far.
fn analyze_assumption_conflict<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut IncrementalP,
        mut ProofP<'a>,
        mut SolverStateP,
        mut TmpDataP,
        ClauseAllocP,
        ImplGraphP,
        TrailP,
    ),
    assumption: Lit,
) {
    let (incremental, mut ctx) = ctx.split_part_mut(IncrementalP);
    let (tmp, mut ctx) = ctx.split_part_mut(TmpDataP);
    let (trail, mut ctx) = ctx.split_part(TrailP);
    let (impl_graph, mut ctx) = ctx.split_part(ImplGraphP);

    let flags = &mut tmp.flags;

    incremental.failed_core.clear();
    incremental.failed_core.push(assumption);

    incremental.failed_propagation_hashes.clear();

    flags[assumption.index()] = true;
    let mut flag_count = 1;

    for &lit in trail.trail().iter().rev() {
        if flags[lit.index()] {
            flags[lit.index()] = false;
            flag_count -= 1;

            match impl_graph.reason(lit.var()) {
                Reason::Unit => {
                    if impl_graph.level(lit.var()) > 0 {
                        incremental.failed_core.push(lit);
                    }
                }
                reason => {
                    let (ctx_lits, ctx) = ctx.split_borrow();
                    let reason_lits = reason.lits(&ctx_lits);

                    if ctx.part(ProofP).clause_hashes_required() {
                        let hash = clause_hash(reason_lits) ^ lit_hash(lit);
                        incremental.failed_propagation_hashes.push(hash);
                    }

                    for &reason_lit in reason_lits {
                        if !flags[reason_lit.index()] {
                            flags[reason_lit.index()] = true;
                            flag_count += 1;
                        }
                    }
                }
            }

            if flag_count == 0 {
                break;
            }
        }
    }

    incremental.failed_propagation_hashes.reverse();

    proof::add_step(
        ctx.borrow(),
        &ProofStep::FailedAssumptions {
            failed_core: &incremental.failed_core,
            propagation_hashes: &incremental.failed_propagation_hashes,
        },
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::{bool, prelude::*};

    use partial_ref::IntoPartialRefMut;

    use varisat_formula::test::conditional_pigeon_hole;

    use crate::cdcl::conflict_step;
    use crate::context::{set_var_count, SolverStateP};
    use crate::load::load_clause;
    use crate::state::SatState;

    proptest! {
        #[test]
        fn pigeon_hole_unsat_assumption_core(
            (enable_row, columns, formula) in conditional_pigeon_hole(1..5usize, 1..5usize),
            chain in bool::ANY,
        ) {
            let mut ctx = Context::default();
            let mut ctx = ctx.into_partial_ref_mut();

            set_var_count(ctx.borrow(), formula.var_count());

            for clause in formula.iter() {
                load_clause(ctx.borrow(), clause);
            }

            if chain {
                for (&a, &b) in enable_row.iter().zip(enable_row.iter().skip(1)) {
                    load_clause(ctx.borrow(), &[!a, b]);
                }
            }

            while ctx.part(SolverStateP).sat_state == SatState::Unknown {
                conflict_step(ctx.borrow());
            }

            prop_assert_eq!(ctx.part(SolverStateP).sat_state, SatState::Sat);

            set_assumptions(ctx.borrow(), &enable_row);

            prop_assert_eq!(ctx.part(SolverStateP).sat_state, SatState::Unknown);

            while ctx.part(SolverStateP).sat_state == SatState::Unknown {
                conflict_step(ctx.borrow());
            }

            prop_assert_eq!(ctx.part(SolverStateP).sat_state, SatState::UnsatUnderAssumptions);

            let mut candidates = ctx.part(IncrementalP).failed_core().to_owned();
            let mut core: Vec<Lit> = vec![];

            loop {
                set_assumptions(ctx.borrow(), &candidates[0..candidates.len() - 1]);

                while ctx.part(SolverStateP).sat_state == SatState::Unknown {
                    conflict_step(ctx.borrow());
                }

                match ctx.part(SolverStateP).sat_state {
                    SatState::Unknown => unreachable!(),
                    SatState::Unsat => break,
                    SatState::Sat => {
                        let skipped = *candidates.last().unwrap();
                        core.push(skipped);
                        load_clause(ctx.borrow(), &[skipped]);
                    },
                    SatState::UnsatUnderAssumptions => {
                        candidates = ctx.part(IncrementalP).failed_core().to_owned();
                    }
                }
            }
            if chain {
                prop_assert_eq!(core.len(), 1);
            } else {
                prop_assert_eq!(core.len(), columns + 1);
            }
        }
    }
}
