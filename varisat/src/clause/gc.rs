//! Garbage collection of long clauses.
use partial_ref::{partial, PartialRef};

use crate::context::{ClauseAllocP, ClauseDbP, Context, ImplGraphP, TrailP, WatchlistsP};
use crate::prop::Reason;

use super::{ClauseAlloc, Tier};

/// Perform a garbage collection of long clauses if necessary.
pub fn collect_garbage(
    mut ctx: partial!(
        Context,
        mut ClauseAllocP,
        mut ClauseDbP,
        mut ImplGraphP,
        mut WatchlistsP,
        TrailP,
    ),
) {
    let alloc = ctx.part(ClauseAllocP);
    let db = ctx.part(ClauseDbP);

    // Collecting when a fixed fraction of the allocation is garbage amortizes collection costs.
    if db.garbage_size * 2 > alloc.buffer_size() {
        collect_garbage_now(ctx.borrow());
    }
}

/// Unconditionally perform a garbage collection of long clauses.
///
/// This needs to invalidate or update any other data structure containing references to
/// clauses.
fn collect_garbage_now(
    mut ctx: partial!(
        Context,
        mut ClauseAllocP,
        mut ClauseDbP,
        mut ImplGraphP,
        mut WatchlistsP,
        TrailP,
    ),
) {
    ctx.part_mut(WatchlistsP).disable();

    mark_asserting_clauses(ctx.borrow());

    let (db, mut ctx) = ctx.split_part_mut(ClauseDbP);
    let (impl_graph, mut ctx) = ctx.split_part_mut(ImplGraphP);
    let alloc = ctx.part_mut(ClauseAllocP);

    assert!(
        db.garbage_size <= alloc.buffer_size(),
        "Inconsistent garbage tracking in ClauseDb"
    );
    let current_size = alloc.buffer_size() - db.garbage_size;

    // Allocating just the current size would lead to an immediate growing when new clauses are
    // learned, overallocating here avoids that.
    let mut new_alloc = ClauseAlloc::with_capacity(current_size * 2);

    let mut new_clauses = vec![];
    let mut new_by_tier: [Vec<_>; Tier::count()] = Default::default();

    // TODO Optimize order of clauses (benchmark this)

    db.clauses.retain(|&cref| {
        let clause = alloc.clause(cref);
        let mut header = clause.header().clone();
        if header.deleted() {
            false
        } else {
            let clause_is_asserting = header.mark();
            header.set_mark(false);

            let new_cref = new_alloc.add_clause(header, clause.lits());

            new_clauses.push(new_cref);
            new_by_tier[header.tier() as usize].push(new_cref);

            if clause_is_asserting {
                let asserted_lit = clause.lits()[0];

                debug_assert_eq!(impl_graph.reason(asserted_lit.var()), &Reason::Long(cref));
                impl_graph.update_reason(asserted_lit.var(), Reason::Long(new_cref));
            }
            true
        }
    });

    *ctx.part_mut(ClauseAllocP) = new_alloc;
    db.clauses = new_clauses;
    db.by_tier = new_by_tier;
    db.garbage_size = 0;
}

/// Mark asserting clauses to track them through GC.
fn mark_asserting_clauses(mut ctx: partial!(Context, mut ClauseAllocP, ImplGraphP, TrailP,)) {
    let (trail, mut ctx) = ctx.split_part(TrailP);
    let (alloc, ctx) = ctx.split_part_mut(ClauseAllocP);
    let impl_graph = ctx.part(ImplGraphP);

    for &lit in trail.trail().iter() {
        if let &Reason::Long(cref) = impl_graph.reason(lit.var()) {
            alloc.header_mut(cref).set_mark(true);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::cmp::max;

    use partial_ref::IntoPartialRefMut;
    use proptest::*;

    use varisat_formula::{cnf::strategy::*, Lit};

    use crate::clause::{db, ClauseHeader};
    use crate::context::{set_var_count, AssignmentP};
    use crate::prop::enqueue_assignment;

    proptest! {
        #[test]
        fn garbage_collection(
            input_a in cnf_formula(2..100usize, 500..1000, 3..30),
            input_b in cnf_formula(2..100usize, 10..500, 4..20),
        ) {
            let mut ctx = Context::default();
            let mut ctx = ctx.into_partial_ref_mut();

            set_var_count(ctx.borrow(), max(input_a.var_count(), input_b.var_count()));

            let mut crefs_a = vec![];
            let mut crefs_b = vec![];

            for lits in input_a.iter() {
                let header = ClauseHeader::new();
                let cref = db::add_clause(ctx.borrow(), header, lits);
                crefs_a.push(cref);
            }

            for lits in input_b.iter() {
                let header = ClauseHeader::new();
                let cref = db::add_clause(ctx.borrow(), header, lits);
                crefs_b.push(cref);

                if ctx.part(AssignmentP).lit_value(lits[0]) == None {
                    // This isn't consistent, as the clause isn't actually propagating, but that
                    // isn't checked during garbage collection
                    enqueue_assignment(ctx.borrow(), lits[0], Reason::Long(cref));
                }
            }

            for cref in crefs_a {
                db::delete_clause(ctx.borrow(), cref);
                prop_assert!(ctx.part(ClauseDbP).garbage_size > 0);
            }

            let old_buffer_size = ctx.part(ClauseAllocP).buffer_size();

            collect_garbage(ctx.borrow());

            prop_assert!(
                ctx.part(ClauseDbP).garbage_size * 2 < ctx.part(ClauseAllocP).buffer_size()
            );

            prop_assert!(
                old_buffer_size > ctx.part(ClauseAllocP).buffer_size()
            );

            prop_assert!(!ctx.part(WatchlistsP).enabled());

            let mut output_clauses: Vec<Vec<Lit>> = vec![];

            for &cref in ctx.part(ClauseDbP).clauses.iter() {
                let clause = ctx.part(ClauseAllocP).clause(cref);
                if clause.header().deleted() {
                    continue;
                }
                prop_assert!(!clause.header().mark());
                output_clauses.push(clause.lits().iter().cloned().collect());
            }

            let mut input_clauses: Vec<Vec<Lit>> = input_b
                .iter()
                .map(|c| c.iter().cloned().collect())
                .collect();

            output_clauses.sort();
            input_clauses.sort();

            prop_assert_eq!(input_clauses, output_clauses);

            for &lit in ctx.part(TrailP).trail() {
                if let &Reason::Long(cref) = ctx.part(ImplGraphP).reason(lit.var()) {
                    prop_assert_eq!(ctx.part(ClauseAllocP).clause(cref).lits()[0], lit)
                }
            }
        }
    }
}
