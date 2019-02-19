//! Central solver data structure.
use partial_ref::{part, partial, PartialRef, PartialRefTarget};

use crate::binary::BinaryClauses;
use crate::clause::{ClauseAlloc, ClauseDb};
use crate::prop::{Assignment, ImplGraph, Trail, Watchlists};
use crate::state::SolverState;
use crate::tmp::TmpData;

/// Part declarations for the [`Context`] struct.
mod parts {
    use super::*;

    part!(pub AssignmentP: Assignment);
    part!(pub BinaryClausesP: BinaryClauses);
    part!(pub ClauseAllocP: ClauseAlloc);
    part!(pub ClauseDbP: ClauseDb);
    part!(pub ImplGraphP: ImplGraph);
    part!(pub SolverStateP: SolverState);
    part!(pub TmpDataP: TmpData);
    part!(pub TrailP: Trail);
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
    #[part = "AssignmentP"]
    assignment: Assignment,
    #[part = "BinaryClausesP"]
    binary_clauses: BinaryClauses,
    #[part = "ClauseAllocP"]
    clause_alloc: ClauseAlloc,
    #[part = "ClauseDbP"]
    clause_db: ClauseDb,
    #[part = "ImplGraphP"]
    impl_graph: ImplGraph,
    #[part = "SolverStateP"]
    solver_state: SolverState,
    #[part = "TmpDataP"]
    tmp_data: TmpData,
    #[part = "TrailP"]
    trail: Trail,
    #[part = "WatchlistsP"]
    watchlists: Watchlists,
}

/// Update structures for a new variable count.
pub fn set_var_count(
    mut ctx: partial!(
        Context,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ImplGraphP,
        mut WatchlistsP,
    ),
    count: usize,
) {
    ctx.part_mut(AssignmentP).set_var_count(count);
    ctx.part_mut(BinaryClausesP).set_var_count(count);
    ctx.part_mut(ImplGraphP).set_var_count(count);
    ctx.part_mut(WatchlistsP).set_var_count(count);
}
