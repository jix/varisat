//! Central solver data structure.
use partial_ref::{part, PartialRefTarget};

use crate::clause::{ClauseAlloc, ClauseDb};

/// Part declarations for the [`Context`] struct.
mod parts {
    use super::*;

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
    #[part = "ClauseDbP"]
    clause_db: ClauseDb,
    #[part = "ClauseAllocP"]
    clause_alloc: ClauseAlloc,
}
