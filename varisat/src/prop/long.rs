//! Propagation of long clauses.
use partial_ref::{partial, PartialRef};

use crate::context::{AssignmentP, ClauseAllocP, Context, ImplGraphP, TrailP, WatchlistsP};
use crate::lit::Lit;

use super::assignment::fast_option_eq;
use super::enqueue_assignment;
use super::{Conflict, Reason, Watch};

/// Propagate all literals implied by long clauses watched by the given literal.
///
/// On conflict return the clause propgating the conflicting assignment.
///
/// See [`prop::watch`](crate::prop::watch) for the invariants that this has to uphold.
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
    // The code below is heavily optimized and replaces a much nicer but sadly slower version.
    // Nevertheless it still performs full bound checks. Therefore this function is safe to call
    // even when some other code violated invariants of for example the clause db.
    unsafe {
        let (watchlists, mut ctx) = ctx.split_part_mut(WatchlistsP);
        let (alloc, mut ctx) = ctx.split_part_mut(ClauseAllocP);

        let watch_begin;
        let watch_end;
        {
            let watch_list = &mut watchlists.watched_by_mut(lit);
            watch_begin = watch_list.as_mut_ptr();
            watch_end = watch_begin.add(watch_list.len());
        }
        let mut watch_ptr = watch_begin;

        let false_lit = !lit;

        let mut watch_write = watch_ptr;

        let assignment_limit = ctx.part(AssignmentP).assignment().len();
        let assignment_ptr = ctx.part(AssignmentP).assignment().as_ptr();

        let is_true = |lit: Lit| {
            assert!(lit.index() < assignment_limit);
            fast_option_eq(*assignment_ptr.add(lit.index()), Some(lit.is_positive()))
        };

        let is_false = |lit: Lit| {
            assert!(lit.index() < assignment_limit);
            fast_option_eq(*assignment_ptr.add(lit.index()), Some(lit.is_negative()))
        };

        'watchers: while watch_ptr != watch_end {
            let watch = *watch_ptr;
            watch_ptr = watch_ptr.add(1);

            // If the blocking literal (which is part of the watched clause) is already true, the
            // watched clause is satisfied and we don't even have to look at it.
            if is_true(watch.blocking) {
                *watch_write = watch;
                watch_write = watch_write.add(1);
                continue;
            }

            let cref = watch.cref;

            // Make sure we can access at least 3 lits
            alloc.check_bounds(cref, 3);

            let clause_ptr = alloc.lits_ptr_mut_unchecked(cref);
            let &mut header = alloc.header_unchecked_mut(cref);

            // First we ensure that the literal we're currently propagating is at index 1. This
            // prepares the literal order for further propagations, as the propagating literal has
            // to be at index 0. Doing this here also avoids a similar check later should the clause
            // be satisfied by a non-watched literal, as we can just move it to index 1.
            let mut first = *clause_ptr.add(0);
            if first == false_lit {
                let c1 = *clause_ptr.add(1);
                first = c1;
                *clause_ptr.add(0) = c1;
                *clause_ptr.add(1) = false_lit;
            }

            // We create a new watch with the other watched literal as blocking literal. This will
            // either replace the currently processed watch or be added to another literals watch
            // list.
            let new_watch = Watch {
                cref: cref,
                blocking: first,
            };

            // If the other watched literal (now the first) isn't the blocking literal, check
            // whether that one is true. If so nothing else needs to be done.
            if first != watch.blocking && is_true(first) {
                *watch_write = new_watch;
                watch_write = watch_write.add(1);
                continue;
            }

            // At this point we try to find a non-false unwatched literal to replace our current
            // literal as the watched literal.

            let clause_len = header.len();
            let mut lit_ptr = clause_ptr.add(2);
            let lit_end = clause_ptr.add(clause_len);

            // Make sure we can access all clause literals.
            alloc.check_bounds(cref, clause_len);

            while lit_ptr != lit_end {
                let rest_lit = *lit_ptr;
                if !is_false(rest_lit) {
                    // We found a non-false literal and make it a watched literal by reordering the
                    // literals and adding the watch to the corresponding watchlist.
                    *clause_ptr.offset(1) = rest_lit;
                    *lit_ptr = false_lit;

                    // We're currently using unsafe to modify the watchlist of lit, so make extra
                    // sure we're not aliasing.
                    assert_ne!(!rest_lit, lit);
                    watchlists.add_watch(!rest_lit, new_watch);
                    continue 'watchers;
                }
                lit_ptr = lit_ptr.add(1);
            }

            // We didn't find a non-false unwatched literal, so either we're propagating or we have
            // a conflict.
            *watch_write = new_watch;
            watch_write = watch_write.add(1);

            // If the other watched literal is false we have a conflict.
            if is_false(first) {
                // We move all unprocessed watches and resize the currentl watchlist.
                while watch_ptr != watch_end {
                    *watch_write = *watch_ptr;
                    watch_write = watch_write.add(1);
                    watch_ptr = watch_ptr.add(1);
                }
                let out_size = ((watch_write as usize) - (watch_begin as usize))
                    / std::mem::size_of::<Watch>();

                watchlists.watched_by_mut(lit).truncate(out_size as usize);

                return Err(Conflict::Long(cref));
            }

            // Otherwise we enqueue a new propagation.
            enqueue_assignment(ctx.borrow(), first, Reason::Long(cref));
        }

        let out_size =
            ((watch_write as usize) - (watch_begin as usize)) / std::mem::size_of::<Watch>();
        watchlists.watched_by_mut(lit).truncate(out_size as usize);
    }
    Ok(())
}
