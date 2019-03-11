//! Scheduling of processing and solving steps.
//!
//! The current implementation is temporary and will be replaced with something more flexible.
use log::info;

use partial_ref::{partial, PartialRef};

use crate::cdcl::conflict_step;
use crate::clause::reduce::{reduce_locals, reduce_mids};
use crate::clause::Tier;
use crate::context::{
    AnalyzeConflictP, AssignmentP, BinaryClausesP, ClauseAllocP, ClauseDbP, Context, ImplGraphP,
    ScheduleP, SolverStateP, TmpDataP, TrailP, VsidsP, WatchlistsP,
};
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
pub fn schedule_step(
    mut ctx: partial!(
        Context,
        mut AnalyzeConflictP,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ClauseAllocP,
        mut ClauseDbP,
        mut ImplGraphP,
        mut ScheduleP,
        mut SolverStateP,
        mut TmpDataP,
        mut TrailP,
        mut VsidsP,
        mut WatchlistsP,
    ),
) -> bool {
    let (schedule, mut ctx) = ctx.split_part_mut(ScheduleP);

    if ctx.part(SolverStateP).sat_state == SatState::Unknown {
        if schedule.conflicts > 0 && schedule.conflicts % 5000 == 0 {
            let db = ctx.part(ClauseDbP);
            let units = ctx.part(TrailP).top_level_trail_length();
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
            schedule.next_restart += 128 * schedule.luby.advance();
        }

        if schedule.conflicts % 15000 == 0 {
            reduce_locals(ctx.borrow());
        }
        if schedule.conflicts % 10000 == 0 {
            reduce_mids(ctx.borrow());
        }

        conflict_step(ctx.borrow());
        schedule.conflicts += 1;
        true
    } else {
        false
    }
}
