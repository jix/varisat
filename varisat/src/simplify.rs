//! Simplification using unit clauses.

use partial_ref::{partial, split_borrow, PartialRef};

use varisat_formula::{Lit, Var};
use varisat_internal_proof::{clause_hash, lit_hash, DeleteClauseProof, ProofStep};

use crate::binary::simplify_binary;
use crate::clause::db::filter_clauses;
use crate::context::{parts::*, Context};
use crate::proof;
use crate::prop::{enqueue_assignment, Reason};
use crate::variables;

/// Remove satisfied clauses and false literals.
pub fn prove_units<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut ImplGraphP,
        mut ProofP<'a>,
        mut SolverStateP,
        mut TrailP,
        AssignmentP,
        ClauseAllocP,
        VariablesP,
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
            proof::add_step(ctx.borrow(), true, &ProofStep::UnitClauses(&unit_proofs));
        }
    }

    new_unit
}

/// Put a removed unit back onto the trail.
pub fn resurrect_unit<'a>(
    mut ctx: partial!(Context<'a>, mut AssignmentP, mut ImplGraphP, mut TrailP),
    lit: Lit,
) {
    // TODO move this somewhere else?
    if ctx.part(ImplGraphP).is_removed_unit(lit.var()) {
        debug_assert!(ctx.part(AssignmentP).lit_is_true(lit));
        ctx.part_mut(AssignmentP).unassign_var(lit.var());

        // Because we always enqueue with Reason::Unit this will not cause a unit clause to be
        // proven in `prove_units`.
        enqueue_assignment(ctx.borrow(), lit, Reason::Unit);
    }
}

/// Remove satisfied clauses and false literals.
pub fn simplify<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ClauseAllocP,
        mut ClauseDbP,
        mut ProofP<'a>,
        mut SolverStateP,
        mut VariablesP,
        mut WatchlistsP,
        mut VsidsP,
        IncrementalP,
    ),
) {
    simplify_binary(ctx.borrow());

    let (assignment, mut ctx) = ctx.split_part(AssignmentP);

    let mut new_lits = vec![];
    {
        split_borrow!(proof_ctx = &(mut ProofP, mut SolverStateP, VariablesP) ctx);
        let (ctx_2, mut ctx) = ctx.split_borrow();

        filter_clauses(ctx_2, |alloc, cref| {
            let clause = alloc.clause_mut(cref);
            let redundant = clause.header().redundant();
            new_lits.clear();
            for &lit in clause.lits() {
                match assignment.lit_value(lit) {
                    None => new_lits.push(lit),
                    Some(true) => {
                        proof::add_step(
                            proof_ctx.borrow(),
                            true,
                            &ProofStep::DeleteClause {
                                clause: clause.lits(),
                                proof: if redundant {
                                    DeleteClauseProof::Redundant
                                } else {
                                    DeleteClauseProof::Satisfied
                                },
                            },
                        );
                        return false;
                    }
                    Some(false) => (),
                }
            }
            if new_lits.len() < clause.lits().len() {
                if proof_ctx.part(ProofP).is_active() {
                    let hash = [clause_hash(clause.lits())];
                    proof::add_step(
                        proof_ctx.borrow(),
                        true,
                        &ProofStep::AtClause {
                            redundant: redundant && new_lits.len() > 2,
                            clause: &new_lits,
                            propagation_hashes: &hash[..],
                        },
                    );
                    proof::add_step(
                        proof_ctx.borrow(),
                        true,
                        &ProofStep::DeleteClause {
                            clause: clause.lits(),
                            proof: if redundant {
                                DeleteClauseProof::Redundant
                            } else {
                                DeleteClauseProof::Simplified
                            },
                        },
                    );
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
        });
    }

    for (var_index, &value) in assignment.assignment().iter().enumerate() {
        let var = Var::from_index(var_index);
        if !ctx.part(VariablesP).solver_var_present(var) {
            continue;
        }
        if let Some(value) = value {
            let var_data = ctx.part_mut(VariablesP).var_data_solver_mut(var);
            var_data.unit = Some(value);
            var_data.isolated = true;
        }
    }

    // TODO use a better way to protect assumptions

    let (incremental, mut ctx) = ctx.split_part(IncrementalP);

    for &lit in incremental.assumptions() {
        let var_data = ctx.part_mut(VariablesP).var_data_solver_mut(lit.var());
        if var_data.unit.is_some() {
            var_data.isolated = false;
        }
    }

    for (var_index, &value) in assignment.assignment().iter().enumerate() {
        let var = Var::from_index(var_index);
        if !ctx.part(VariablesP).solver_var_present(var) {
            continue;
        }
        if value.is_some() {
            let var_data = ctx.part_mut(VariablesP).var_data_solver_mut(var);
            if var_data.isolated == true {
                variables::remove_solver_var(ctx.borrow(), var);
            }
        }
    }
}
