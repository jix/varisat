//! Central solver data structure.
use partial_ref::{part, partial, PartialRef, PartialRefTarget};

use crate::binary::BinaryClauses;
use crate::clause::{ClauseAlloc, ClauseDb};

/// Part declarations for the [`Context`] struct.
mod parts {
    use super::*;

    part!(pub BinaryClausesP: BinaryClauses);
    part!(pub ClauseAllocP: ClauseAlloc);
    part!(pub ClauseDbP: ClauseDb);
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
    #[part = "BinaryClausesP"]
    binary_clauses: BinaryClauses,
    #[part = "ClauseAllocP"]
    clause_alloc: ClauseAlloc,
    #[part = "ClauseDbP"]
    clause_db: ClauseDb,
}

/// Update structures for a new variable count.
pub fn set_var_count(
    mut ctx: partial!(
        Context,
        mut BinaryClausesP,
    ),
    count: usize,
) {
    ctx.part_mut(BinaryClausesP).set_var_count(count);
}
