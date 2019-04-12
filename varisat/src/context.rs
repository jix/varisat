//! Central solver data structure.
use partial_ref::{part, partial, PartialRef, PartialRefTarget};

use crate::analyze_conflict::AnalyzeConflict;
use crate::binary::BinaryClauses;
use crate::clause::{ClauseActivity, ClauseAlloc, ClauseDb};
use crate::decision::vsids::Vsids;
use crate::incremental::Incremental;
use crate::proof::Proof;
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
    part!(pub IncrementalP: Incremental);
    part!(pub ProofP<'a>: Proof<'a>);
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
pub struct Context<'a> {
    #[part(AnalyzeConflictP)]
    pub analyze_conflict: AnalyzeConflict,
    #[part(AssignmentP)]
    pub assignment: Assignment,
    #[part(BinaryClausesP)]
    pub binary_clauses: BinaryClauses,
    #[part(ClauseActivityP)]
    pub clause_activity: ClauseActivity,
    #[part(ClauseAllocP)]
    pub clause_alloc: ClauseAlloc,
    #[part(ClauseDbP)]
    pub clause_db: ClauseDb,
    #[part(ImplGraphP)]
    pub impl_graph: ImplGraph,
    #[part(IncrementalP)]
    pub incremental: Incremental,
    #[part(ProofP<'a>)]
    pub proof: Proof<'a>,
    #[part(ScheduleP)]
    pub schedule: Schedule,
    #[part(SolverStateP)]
    pub solver_state: SolverState,
    #[part(TmpDataP)]
    pub tmp_data: TmpData,
    #[part(TrailP)]
    pub trail: Trail,
    #[part(VsidsP)]
    pub vsids: Vsids,
    #[part(WatchlistsP)]
    pub watchlists: Watchlists,
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
