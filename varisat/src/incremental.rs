//! Incremental solving.

use partial_ref::{partial, PartialRef};

use varisat_formula::Lit;
use varisat_internal_proof::{clause_hash, lit_hash, ClauseHash, ProofStep};

use crate::context::{parts::*, Context};
use crate::proof;
use crate::prop::{enqueue_assignment, full_restart, Reason};
use crate::state::SatState;
use crate::variables;

/// Incremental solving.
#[derive(Default)]
pub struct Incremental {
    assumptions: Vec<Lit>,
    failed_core: Vec<Lit>,
    user_failed_core: Vec<Lit>,
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

    /// Subset of assumptions that made the formula unsatisfiable.
    pub fn user_failed_core(&self) -> &[Lit] {
        &self.user_failed_core
    }

    /// Current assumptions.
    pub fn assumptions(&self) -> &[Lit] {
        &self.assumptions
    }
}

/// Return type of [`enqueue_assumption`].
pub enum EnqueueAssumption {
    Done,
    Enqueued,
    Conflict,
}

/// Change the currently active assumptions.
///
/// The input uses user variable names.
pub fn set_assumptions<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut AnalyzeConflictP,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ImplGraphP,
        mut IncrementalP,
        mut ProofP<'a>,
        mut SolverStateP,
        mut TmpFlagsP,
        mut TrailP,
        mut VariablesP,
        mut VsidsP,
        mut WatchlistsP,
    ),
    user_assumptions: &[Lit],
) {
    full_restart(ctx.borrow());

    let state = ctx.part_mut(SolverStateP);

    state.sat_state = match state.sat_state {
        SatState::Unsat => SatState::Unsat,
        SatState::Sat | SatState::UnsatUnderAssumptions | SatState::Unknown => SatState::Unknown,
    };

    let (incremental, mut ctx_2) = ctx.split_part_mut(IncrementalP);

    for lit in incremental.assumptions.iter() {
        ctx_2
            .part_mut(VariablesP)
            .var_data_solver_mut(lit.var())
            .assumed = false;
    }

    variables::solver_from_user_lits(
        ctx_2.borrow(),
        &mut incremental.assumptions,
        user_assumptions,
        true,
    );

    for lit in incremental.assumptions.iter() {
        ctx_2
            .part_mut(VariablesP)
            .var_data_solver_mut(lit.var())
            .assumed = true;
    }

    proof::add_step(
        ctx_2.borrow(),
        true,
        &ProofStep::Assumptions {
            assumptions: &incremental.assumptions,
        },
    );
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
        mut TmpFlagsP,
        mut TrailP,
        ClauseAllocP,
        VariablesP,
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
        mut TmpFlagsP,
        ClauseAllocP,
        ImplGraphP,
        TrailP,
        VariablesP,
    ),
    assumption: Lit,
) {
    let (incremental, mut ctx) = ctx.split_part_mut(IncrementalP);
    let (tmp, mut ctx) = ctx.split_part_mut(TmpFlagsP);
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

    incremental.user_failed_core.clear();
    incremental
        .user_failed_core
        .extend(incremental.failed_core.iter().map(|solver_lit| {
            let user_lit = solver_lit
                .map_var(|solver_var| ctx.part(VariablesP).existing_user_from_solver(solver_var));
            user_lit
        }));

    proof::add_step(
        ctx.borrow(),
        true,
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

            let mut candidates = ctx.part(IncrementalP).user_failed_core().to_owned();
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
                        candidates = ctx.part(IncrementalP).user_failed_core().to_owned();
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
