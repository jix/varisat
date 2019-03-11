//! Clause assessment.
use partial_ref::{partial, PartialRef};

use crate::context::{Context, ImplGraphP, TmpDataP};
use crate::glue::compute_glue;
use crate::lit::Lit;

use super::{ClauseHeader, Tier};

/// Assess the newly learned clause and generate a clause header.
pub fn assess_learned_clause(
    mut ctx: partial!(Context, mut TmpDataP, ImplGraphP),
    lits: &[Lit],
) -> ClauseHeader {
    // This is called while the clause is still in conflict, thus the computed glue level is one
    // higher than it'll be after backtracking when the clause becomes asserting.
    let glue = compute_glue(ctx.borrow(), lits) - 1;

    let mut header = ClauseHeader::new();

    header.set_glue(glue);
    header.set_tier(select_tier(glue));

    header
}

/// Compute the tier for a redundant clause with a given glue level.
fn select_tier(glue: usize) -> Tier {
    if glue <= 2 {
        Tier::Core
    } else if glue <= 6 {
        Tier::Mid
    } else {
        Tier::Local
    }
}
