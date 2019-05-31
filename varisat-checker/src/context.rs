//! Central checker data structure.
use partial_ref::{part, PartialRefTarget};

use crate::clauses::Clauses;
use crate::hash::ClauseHasher;
use crate::processing::Processing;
use crate::rup::RupCheck;
use crate::state::CheckerState;
use crate::tmp::TmpData;
use crate::variables::Variables;

/// Part declarations for the [`Context`] struct.
pub mod parts {
    use super::*;

    part!(pub CheckerStateP: CheckerState);
    part!(pub ClauseHasherP: ClauseHasher);
    part!(pub ClausesP: Clauses);
    part!(pub ProcessingP<'a>: Processing<'a>);
    part!(pub RupCheckP: RupCheck);
    part!(pub TmpDataP: TmpData);
    part!(pub VariablesP: Variables);
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
    #[part(CheckerStateP)]
    pub checker_state: CheckerState,
    #[part(ClauseHasherP)]
    pub clause_hasher: ClauseHasher,
    #[part(ClausesP)]
    pub clauses: Clauses,
    #[part(ProcessingP<'a>)]
    pub processing: Processing<'a>,
    #[part(RupCheckP)]
    pub rup_check: RupCheck,
    #[part(TmpDataP)]
    pub tmp_data: TmpData,
    #[part(VariablesP)]
    pub variables: Variables,
}
