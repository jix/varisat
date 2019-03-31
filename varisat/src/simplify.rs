//! Simplification using unit clauses.

use partial_ref::{partial, PartialRef};

use crate::binary::simplify_binary;
use crate::clause::db::filter_clauses;
use crate::context::{
    AssignmentP, BinaryClausesP, ClauseAllocP, ClauseDbP, Context, ImplGraphP, ProofP, TrailP,
    WatchlistsP,
};
use crate::proof::{clause_hash, lit_hash, ProofStep};

/// Remove satisfied clauses and false literals.
pub fn prove_units(
    mut ctx: partial!(
        Context,
        mut ImplGraphP,
        mut ProofP,
        mut TrailP,
        AssignmentP,
        ClauseAllocP,
    ),
) -> bool {
    // TODO move this somewhere else?

    let mut new_unit = false;

    if ctx.part(TrailP).current_level() == 0 {
        let (impl_graph, mut ctx) = ctx.split_part_mut(ImplGraphP);

        let mut unit_proofs = vec![];

        let (trail, mut ctx) = ctx.split_part_mut(TrailP);

        for &lit in trail.trail() {
            new_unit = true;
            let (proof, mut ctx) = ctx.split_part_mut(ProofP);
            if proof.prove_propagated_unit_clauses() {
                let ctx_lits = ctx.borrow();
                let reason = impl_graph.reason(lit.var());
                if !reason.is_unit() {
                    let lits = impl_graph.reason(lit.var()).lits(&ctx_lits);
                    let hash = clause_hash(lits) ^ lit_hash(lit);

                    unit_proofs.push((lit, hash));
                }
            }

            impl_graph.update_removed_unit(lit.var());
        }

        trail.clear();

        if !unit_proofs.is_empty() {
            ctx.part_mut(ProofP)
                .add_step(&ProofStep::UnitClauses(unit_proofs.into()));
        }
    }

    new_unit
}

/// Remove satisfied clauses and false literals.
pub fn simplify(
    mut ctx: partial!(
        Context,
        mut BinaryClausesP,
        mut ClauseAllocP,
        mut ClauseDbP,
        mut ProofP,
        mut WatchlistsP,
        AssignmentP,
    ),
) {
    simplify_binary(ctx.borrow());

    let (assignment, mut ctx) = ctx.split_part(AssignmentP);

    let mut new_lits = vec![];

    let (proof, mut ctx) = ctx.split_part_mut(ProofP);
    let (ctx_2, mut ctx) = ctx.split_borrow();

    filter_clauses(ctx_2, |alloc, cref| {
        let clause = alloc.clause_mut(cref);
        new_lits.clear();
        for &lit in clause.lits() {
            match assignment.lit_value(lit) {
                None => new_lits.push(lit),
                Some(true) => {
                    proof.add_step(&ProofStep::DeleteClause(clause.lits().into()));
                    return false;
                }
                Some(false) => (),
            }
        }
        if new_lits.len() < clause.lits().len() {
            if proof.is_active() {
                let hash = [clause_hash(clause.lits())];
                proof.add_step(&ProofStep::AtClause {
                    clause: new_lits[..].into(),
                    propagation_hashes: hash[..].into(),
                });
                proof.add_step(&ProofStep::DeleteClause(clause.lits().into()));
            }

            match new_lits[..] {
                // Cannot have empty or unit clauses after full propagation. An empty clause would
                // have been a conflict and a unit clause must be satisfied and thus would have been
                // dropped above.
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
        } else {
            true
        }
    })
}
