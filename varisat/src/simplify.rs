//! Simplification using unit clauses.

use partial_ref::{partial, PartialRef};

use crate::binary::simplify_binary;
use crate::clause::db::filter_clauses;
use crate::context::{
    AssignmentP, BinaryClausesP, ClauseAllocP, ClauseDbP, Context, ImplGraphP, TrailP, WatchlistsP,
};
use crate::prop::Reason;

/// Remove satisfied clauses and false literals.
pub fn simplify(
    mut ctx: partial!(
        Context,
        mut BinaryClausesP,
        mut ClauseAllocP,
        mut ClauseDbP,
        mut ImplGraphP,
        mut TrailP,
        mut WatchlistsP,
        AssignmentP,
    ),
) {
    assert_eq!(ctx.part(TrailP).current_level(), 0);
    assert!(ctx.part(TrailP).fully_propagated());

    let (impl_graph, mut ctx) = ctx.split_part_mut(ImplGraphP);
    for &lit in ctx.part(TrailP).trail().iter() {
        // TODO emit proof of unit clause
        impl_graph.update_reason(lit.var(), Reason::Unit)
    }

    ctx.part_mut(TrailP).clear();

    simplify_binary(ctx.borrow());

    let (assignment, mut ctx) = ctx.split_part(AssignmentP);

    let mut new_lits = vec![];

    filter_clauses(ctx.borrow(), |alloc, cref| {
        let clause = alloc.clause_mut(cref);
        new_lits.clear();
        for &lit in clause.lits() {
            match assignment.lit_value(lit) {
                None => new_lits.push(lit),
                Some(true) => return false,
                Some(false) => (),
            }
        }
        match new_lits[..] {
            // Cannot have empty or unit clauses after full propagation. An empty clause would have
            // been a conflict and a unit clause must be satisfied and thus would have been dropped
            // above.
            [] | [_] => unreachable!(),
            [lit_0, lit_1] => {
                ctx.part_mut(BinaryClausesP)
                    .add_binary_clause([lit_0, lit_1]);
                false
            }
            ref lits => {
                clause.lits_mut()[..lits.len()].copy_from_slice(lits);
                clause.header_mut().set_len(lits.len());
                true
            }
        }
    })
}
