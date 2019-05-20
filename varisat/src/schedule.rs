//! Scheduling of processing and solving steps.
//!
//! The current implementation is temporary and will be replaced with something more flexible.
use log::info;

use partial_ref::{partial, PartialRef};

use crate::cdcl::conflict_step;
use crate::clause::reduce::{reduce_locals, reduce_mids};
use crate::clause::{collect_garbage, Tier};
use crate::context::{parts::*, Context};
use crate::prop::restart;
use crate::state::SatState;

mod luby;

use luby::LubySequence;

/// Scheduling of processing and solving steps.
#[derive(Default)]
pub struct Schedule {
    conflicts: u64,
    next_restart: u64,
    restarts: u64,
    luby: LubySequence,
}

/// Perform one step of the schedule.
pub fn schedule_step<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut AnalyzeConflictP,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ClauseActivityP,
        mut ClauseAllocP,
        mut ClauseDbP,
        mut ImplGraphP,
        mut IncrementalP,
        mut ProofP<'a>,
        mut ScheduleP,
        mut SolverStateP,
        mut TmpDataP,
        mut TrailP,
        mut VsidsP,
        mut WatchlistsP,
        SolverConfigP,
        VariablesP,
    ),
) -> bool {
    let (schedule, mut ctx) = ctx.split_part_mut(ScheduleP);
    let (config, mut ctx) = ctx.split_part(SolverConfigP);

    if ctx.part(SolverStateP).sat_state != SatState::Unknown {
        false
    } else if ctx.part(SolverStateP).solver_error.is_some() {
        false
    } else {
        if schedule.conflicts > 0 && schedule.conflicts % 5000 == 0 {
            let db = ctx.part(ClauseDbP);
            let units = ctx.part(TrailP).top_level_assignment_count();
            info!(
                "confl: {}k rest: {} vars: {} bin: {} irred: {} core: {} mid: {} local: {}",
                schedule.conflicts / 1000,
                schedule.restarts,
                ctx.part(AssignmentP).assignment().len() - units,
                ctx.part(BinaryClausesP).count(),
                db.count_by_tier(Tier::Irred),
                db.count_by_tier(Tier::Core),
                db.count_by_tier(Tier::Mid),
                db.count_by_tier(Tier::Local)
            );
        }

        if schedule.next_restart == schedule.conflicts {
            restart(ctx.borrow());
            schedule.restarts += 1;
            schedule.next_restart += config.luby_restart_interval_scale * schedule.luby.advance();
        }

        if schedule.conflicts % config.reduce_locals_interval == 0 {
            reduce_locals(ctx.borrow());
        }
        if schedule.conflicts % config.reduce_mids_interval == 0 {
            reduce_mids(ctx.borrow());
        }

        collect_garbage(ctx.borrow());

        conflict_step(ctx.borrow());
        schedule.conflicts += 1;
        true
    }
}
