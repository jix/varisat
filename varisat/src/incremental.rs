//! Incremental solving.

use partial_ref::{partial, PartialRef};

use crate::context::{
    AssignmentP, ClauseAllocP, Context, ImplGraphP, IncrementalP, SolverStateP, TmpDataP, TrailP,
    VsidsP,
};
use crate::lit::Lit;
use crate::prop::{enqueue_assignment, full_restart, Reason};
use crate::state::SatState;

/// Incremental solving.
#[derive(Default)]
pub struct Incremental {
    assumptions: Vec<Lit>,
    failed_core: Vec<Lit>,
    assumption_levels: usize,
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
pub fn set_assumptions(
    mut ctx: partial!(
        Context,
        mut AssignmentP,
        mut IncrementalP,
        mut SolverStateP,
        mut TrailP,
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
}

/// Enqueue another assumption if possible.
///
/// Returns whether an assumption was enqueued, whether no assumptions are left or whether the
/// assumptions result in a conflict.
pub fn enqueue_assumption(
    mut ctx: partial!(
        Context,
        mut AssignmentP,
        mut ImplGraphP,
        mut IncrementalP,
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
fn analyze_assumption_conflict(
    mut ctx: partial!(
        Context,
        mut IncrementalP,
        mut TmpDataP,
        ClauseAllocP,
        ImplGraphP,
        TrailP,
    ),
    assumption: Lit,
) {
    let (incremental, mut ctx) = ctx.split_part_mut(IncrementalP);
    let (tmp, ctx) = ctx.split_part_mut(TmpDataP);

    let flags = &mut tmp.flags;

    incremental.failed_core.clear();
    incremental.failed_core.push(assumption);

    flags[assumption.index()] = true;
    let mut flag_count = 1;

    for &lit in ctx.part(TrailP).trail().iter().rev() {
        if flags[lit.index()] {
            flags[lit.index()] = false;
            flag_count -= 1;

            match ctx.part(ImplGraphP).reason(lit.var()) {
                Reason::Unit => {
                    if ctx.part(ImplGraphP).level(lit.var()) > 0 {
                        incremental.failed_core.push(lit);
                    }
                }
                reason => {
                    for &reason_lit in reason.lits(&ctx.clone().borrow()) {
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
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::{bool, prelude::*};

    use partial_ref::IntoPartialRefMut;

    use crate::cdcl::conflict_step;
    use crate::context::{set_var_count, SolverStateP};
    use crate::load::load_clause;
    use crate::state::SatState;

    use crate::test::conditional_pigeon_hole;

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
