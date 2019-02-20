//! Propagation of long clauses.
use std::mem::replace;

use partial_ref::{partial, PartialRef};

use crate::context::{AssignmentP, ClauseAllocP, Context, ImplGraphP, TrailP, WatchlistsP};
use crate::lit::Lit;
use crate::vec_mut_scan::VecMutScan;

use super::enqueue_assignment;
use super::{Conflict, Reason, Watch};

/// Propagate all literals implied by long clauses watched by the given literal.
///
/// On conflict return the clause propgating the conflicting assignment.
///
/// See [`prop::watch`](crate::prop::watch) for the invariants that this has to uphold.
#[inline(never)]
pub fn propagate_long(
    mut ctx: partial!(
        Context,
        mut AssignmentP,
        mut ImplGraphP,
        mut TrailP,
        mut WatchlistsP,
        mut ClauseAllocP,
    ),
    lit: Lit,
) -> Result<(), Conflict> {
    // Temporarily move watches out of the watchlists struct, so we are free to add watches to other
    // lists during propagation.
    let mut watches = replace(ctx.part_mut(WatchlistsP).watched_by_mut(lit), vec![]);

    let mut scan = VecMutScan::new(&mut watches);

    let mut result = Ok(());

    'watches: while let Some(watch) = scan.next() {
        // If the blocking literal (which is part of the watched clause) is already true, the
        // watched clause is satisfied and we don't even have to look at it.
        if ctx.part(AssignmentP).lit_is_true(watch.blocking) {
            continue;
        }

        let cref = watch.cref;

        let clause = ctx.part_mut(ClauseAllocP).clause_mut(cref);

        let lits = clause.lits_mut();

        // First we ensure that the literal we're currently propagating is at index 1. This prepares
        // the literal order for further propagations, as the propagating literal has to be at index
        // 0. Doing this here also avoids a similar check later should the clause be satisfied by a
        // non-watched literal, as we can just move it to index 1.
        let mut first = lits[0];
        if first == !lit {
            lits.swap(0, 1);
            first = lits[0];
        }

        // We create a new watch with the other watched literal as blocking literal. This will
        // either replace the currently processed watch or be added to another literals watch list.
        let new_watch = Watch {
            cref,
            blocking: first,
        };

        // If the other watched literal (now the first) isn't the blocking literal, check whether
        // that one is true. If so nothing else needs to be done.
        if first != watch.blocking && ctx.part(AssignmentP).lit_is_true(first) {
            watch.replace(new_watch);
            continue;
        }

        // At this point we try to find a non-false unwatched literal to replace our current literal
        // as the watched literal.
        let (initial, rest) = lits.split_at_mut(2);

        for rest_lit_ref in rest.iter_mut() {
            let rest_lit = *rest_lit_ref;
            if !ctx.part(AssignmentP).lit_is_false(rest_lit) {
                // We found a non-false literal and make it a watched literal by reordering the
                // literals and adding the watch to the corresponding watchlist.
                initial[1] = rest_lit;
                *rest_lit_ref = !lit;
                ctx.part_mut(WatchlistsP).add_watch(!rest_lit, new_watch);
                watch.remove();
                continue 'watches;
            }
        }

        // We didn't find a non-false unwatched literal, so either we're propagating or we have a
        // conflict.
        watch.replace(new_watch);

        // If the other watched literal is false we have a conflict.
        if ctx.part(AssignmentP).lit_is_false(first) {
            result = Err(Conflict::Long(cref));
            break;
        }

        // Otherwise we enqueue a new propagation.
        enqueue_assignment(ctx.borrow(), first, Reason::Long(cref));
    }

    // This keeps all unprocessed watches in the current watchlist.
    drop(scan);

    *ctx.part_mut(WatchlistsP).watched_by_mut(lit) = watches;

    result
}
