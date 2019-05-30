//! Central checker data structure.
use partial_ref::{part, PartialRefTarget};

use crate::state::CheckerState;

/// Part declarations for the [`Context`] struct.
pub mod parts {
    use super::*;

    part!(pub CheckerStateP<'a>: CheckerState<'a>);
}

use parts::*;

/// Central checker data structure.
///
/// This struct contains all data kept by the checker. Most functions operating on multiple fields
/// of the context use partial references provided by the `partial_ref` crate. This documents the
/// data dependencies and makes the borrow checker happy without the overhead of passing individual
/// references.
#[derive(PartialRefTarget, Default)]
pub struct Context<'a> {
    #[part(CheckerStateP<'a>)]
    pub checker_state: CheckerState<'a>,
}
