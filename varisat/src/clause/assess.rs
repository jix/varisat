//! Clause assessment.
use partial_ref::{partial, PartialRef};

use varisat_formula::Lit;

use crate::clause::{db, ClauseRef};
use crate::context::{parts::*, Context};
use crate::glue::compute_glue;

use super::{bump_clause_activity, ClauseHeader, Tier};

/// Assess the newly learned clause and generate a clause header.
pub fn assess_learned_clause(
    mut ctx: partial!(Context, mut TmpFlagsP, ImplGraphP),
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

/// Update stats for clauses involved in the conflict.
pub fn bump_clause(
    mut ctx: partial!(
        Context,
        mut ClauseActivityP,
        mut ClauseAllocP,
        mut ClauseDbP,
        mut TmpFlagsP,
        ImplGraphP
    ),
    cref: ClauseRef,
) {
    bump_clause_activity(ctx.borrow(), cref);

    let (alloc, mut ctx_2) = ctx.split_part_mut(ClauseAllocP);

    let clause = alloc.clause_mut(cref);

    let glue = compute_glue(ctx_2.borrow(), clause.lits());

    clause.header_mut().set_active(true);

    if glue < clause.header().glue() {
        clause.header_mut().set_glue(glue);

        db::set_clause_tier(ctx.borrow(), cref, select_tier(glue));
    }
}
