//! Binary clauses.

use partial_ref::{partial, PartialRef};

use crate::context::{AssignmentP, BinaryClausesP, Context, ProofP};
use crate::proof::ProofStep;

use crate::lit::Lit;

/// Binary clauses.
#[derive(Default)]
pub struct BinaryClauses {
    by_lit: Vec<Vec<Lit>>,
    count: usize,
}

impl BinaryClauses {
    /// Update structures for a new variable count.
    pub fn set_var_count(&mut self, count: usize) {
        self.by_lit.resize(count * 2, vec![]);
    }

    /// Add a binary clause.
    pub fn add_binary_clause(&mut self, lits: [Lit; 2]) {
        for i in 0..2 {
            self.by_lit[(!lits[i]).code()].push(lits[i ^ 1]);
        }
        self.count += 1;
    }

    /// Implications of a given literal
    pub fn implied(&self, lit: Lit) -> &[Lit] {
        &self.by_lit[lit.code()]
    }

    /// Number of binary clauses.
    pub fn count(&self) -> usize {
        self.count
    }
}

/// Remove binary clauses that have an assigned literal.
pub fn simplify_binary<'a>(
    mut ctx: partial!(Context<'a>, mut BinaryClausesP, mut ProofP<'a>, AssignmentP),
) {
    let (binary_clauses, mut ctx) = ctx.split_part_mut(BinaryClausesP);
    let (proof, ctx) = ctx.split_part_mut(ProofP);
    let assignment = ctx.part(AssignmentP);

    let mut double_count = 0;

    for (code, implied) in binary_clauses.by_lit.iter_mut().enumerate() {
        let lit = Lit::from_code(code);

        if !assignment.lit_is_unk(lit) {
            if proof.is_active() {
                for &other_lit in implied.iter() {
                    // This check avoids deleting binary clauses twice if both literals are assigned.
                    if (!lit) < other_lit {
                        let lits = [!lit, other_lit];
                        proof.add_step(&ProofStep::DeleteClause(lits[..].into()));
                    }
                }
            }

            implied.clear();
        } else {
            implied.retain(|&other_lit| {
                let retain = assignment.lit_is_unk(other_lit);
                // This check avoids deleting binary clauses twice if both literals are assigned.
                if proof.is_active() && !retain && (!lit) < other_lit {
                    let lits = [!lit, other_lit];
                    proof.add_step(&ProofStep::DeleteClause(lits[..].into()));
                }

                retain
            });

            double_count += implied.len();
        }
    }

    binary_clauses.count = double_count / 2;
}
