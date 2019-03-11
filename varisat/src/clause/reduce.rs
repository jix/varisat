//! Clause database reduction.
use std::mem::replace;

use partial_ref::{partial, PartialRef};

use crate::context::{AssignmentP, ClauseAllocP, ClauseDbP, Context, ImplGraphP, WatchlistsP};
use crate::vec_mut_scan::VecMutScan;

use super::db::{set_clause_tier, try_delete_clause, Tier};

/// Remove deleted and duplicate entries from the by_tier clause lists.
///
/// This has the side effect of setting the mark bit on all clauses of the tier.
pub fn dedup_and_mark_by_tier(
    mut ctx: partial!(Context, mut ClauseAllocP, mut ClauseDbP),
    tier: Tier,
) {
    let (alloc, mut ctx) = ctx.split_part_mut(ClauseAllocP);
    let by_tier = &mut ctx.part_mut(ClauseDbP).by_tier[tier as usize];

    by_tier.retain(|&cref| {
        let header = alloc.header_mut(cref);
        let retain = !header.deleted() && !header.mark() && header.tier() == tier;
        if retain {
            header.set_mark(true);
        }
        retain
    })
}

/// Reduce the number of local tier clauses by deleting half of them.
pub fn reduce_locals(
    mut ctx: partial!(
        Context,
        mut ClauseAllocP,
        mut ClauseDbP,
        mut WatchlistsP,
        AssignmentP,
        ImplGraphP
    ),
) {
    dedup_and_mark_by_tier(ctx.borrow(), Tier::Local);

    let mut locals = replace(
        &mut ctx.part_mut(ClauseDbP).by_tier[Tier::Local as usize],
        vec![],
    );

    // TODO this should be activity not glue, but we don't track activities yet.
    locals.sort_unstable_by_key(|&cref| -(ctx.part(ClauseAllocP).header(cref).glue() as isize));

    let mut to_delete = locals.len() / 2;

    let mut scan = VecMutScan::new(&mut locals);

    if to_delete > 0 {
        while let Some(cref) = scan.next() {
            ctx.part_mut(ClauseAllocP).header_mut(*cref).set_mark(false);

            if try_delete_clause(ctx.borrow(), *cref) {
                cref.remove();
                to_delete -= 1;
                if to_delete == 0 {
                    break;
                }
            }
        }
    }

    // Make sure to clear all marks
    while let Some(cref) = scan.next() {
        ctx.part_mut(ClauseAllocP).header_mut(*cref).set_mark(false);
    }

    drop(scan);

    ctx.part_mut(ClauseDbP).count_by_tier[Tier::Local as usize] = locals.len();
    ctx.part_mut(ClauseDbP).by_tier[Tier::Local as usize] = locals;
}

/// Reduce the number of mid tier clauses by moving inactive ones to the local tier.
pub fn reduce_mids(mut ctx: partial!(Context, mut ClauseAllocP, mut ClauseDbP)) {
    dedup_and_mark_by_tier(ctx.borrow(), Tier::Mid);

    let mut mids = replace(
        &mut ctx.part_mut(ClauseDbP).by_tier[Tier::Mid as usize],
        vec![],
    );

    mids.retain(|&cref| {
        let header = ctx.part_mut(ClauseAllocP).header_mut(cref);
        header.set_mark(false);

        if header.active() {
            header.set_active(false);
            true
        } else {
            set_clause_tier(ctx.borrow(), cref, Tier::Local);
            false
        }
    });

    ctx.part_mut(ClauseDbP).count_by_tier[Tier::Mid as usize] = mids.len();
    ctx.part_mut(ClauseDbP).by_tier[Tier::Mid as usize] = mids;
}
