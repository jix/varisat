//! Central solver data structure.
use partial_ref::{part, partial, PartialRef, PartialRefTarget};

use crate::analyze_conflict::AnalyzeConflict;
use crate::binary::BinaryClauses;
use crate::clause::{ClauseActivity, ClauseAlloc, ClauseDb};
use crate::decision::vsids::Vsids;
use crate::prop::{Assignment, ImplGraph, Trail, Watchlists};
use crate::schedule::Schedule;
use crate::state::SolverState;
use crate::tmp::TmpData;

/// Part declarations for the [`Context`] struct.
mod parts {
    use super::*;

    part!(pub AnalyzeConflictP: AnalyzeConflict);
    part!(pub AssignmentP: Assignment);
    part!(pub BinaryClausesP: BinaryClauses);
    part!(pub ClauseActivityP: ClauseActivity);
    part!(pub ClauseAllocP: ClauseAlloc);
    part!(pub ClauseDbP: ClauseDb);
    part!(pub ImplGraphP: ImplGraph);
    part!(pub ScheduleP: Schedule);
    part!(pub SolverStateP: SolverState);
    part!(pub TmpDataP: TmpData);
    part!(pub TrailP: Trail);
    part!(pub VsidsP: Vsids);
    part!(pub WatchlistsP: Watchlists);
}

pub use parts::*;

/// Central solver data structure.
///
/// This struct contains all data kept by the solver. Most functions operating on multiple fields of
/// the context use partial references provided by the `partial_ref` crate. This documents the data
/// dependencies and makes the borrow checker happy without the overhead of passing individual
/// references.
#[derive(PartialRefTarget, Default)]
pub struct Context {
    #[part = "AnalyzeConflictP"]
    analyze_conflict: AnalyzeConflict,
    #[part = "AssignmentP"]
    assignment: Assignment,
    #[part = "BinaryClausesP"]
    binary_clauses: BinaryClauses,
    #[part = "ClauseActivityP"]
    clause_activity: ClauseActivity,
    #[part = "ClauseAllocP"]
    clause_alloc: ClauseAlloc,
    #[part = "ClauseDbP"]
    clause_db: ClauseDb,
    #[part = "ImplGraphP"]
    impl_graph: ImplGraph,
    #[part = "ScheduleP"]
    schedule: Schedule,
    #[part = "SolverStateP"]
    solver_state: SolverState,
    #[part = "TmpDataP"]
    tmp_data: TmpData,
    #[part = "TrailP"]
    trail: Trail,
    #[part = "VsidsP"]
    vsids: Vsids,
    #[part = "WatchlistsP"]
    watchlists: Watchlists,
}

/// Update structures for a new variable count.
pub fn set_var_count(
    mut ctx: partial!(
        Context,
        mut AnalyzeConflictP,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ImplGraphP,
        mut TmpDataP,
        mut VsidsP,
        mut WatchlistsP,
    ),
    count: usize,
) {
    ctx.part_mut(AnalyzeConflictP).set_var_count(count);
    ctx.part_mut(AssignmentP).set_var_count(count);
    ctx.part_mut(BinaryClausesP).set_var_count(count);
    ctx.part_mut(ImplGraphP).set_var_count(count);
    ctx.part_mut(TmpDataP).set_var_count(count);
    ctx.part_mut(VsidsP).set_var_count(count);
    ctx.part_mut(WatchlistsP).set_var_count(count);
}

/// Increases the variable count to at least the given value.
pub fn ensure_var_count(
    mut ctx: partial!(
        Context,
        mut AnalyzeConflictP,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ImplGraphP,
        mut TmpDataP,
        mut VsidsP,
        mut WatchlistsP,
    ),
    count: usize,
) {
    if count > ctx.part_mut(AssignmentP).assignment().len() {
        set_var_count(ctx.borrow(), count)
    }
}
