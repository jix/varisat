//! Maps literals and hashes of clause steps between the solver and the checker.

use crate::lit::Lit;

use super::{ClauseHash, ProofStep};

/// Maps literals and hashes of clause steps between the solver and the checker.
#[derive(Default)]
pub struct MapStep {
    lit_buf: Vec<Lit>,
    hash_buf: Vec<ClauseHash>,
    unit_buf: Vec<(Lit, ClauseHash)>,
}

impl MapStep {
    pub fn map<'s, 'a, 'b>(
        &'a mut self,
        step: &ProofStep<'b>,
        map_lit: impl Fn(Lit) -> Lit,
        map_hash: impl Fn(ClauseHash) -> ClauseHash,
    ) -> ProofStep<'s>
    where
        'a: 's,
        'b: 's,
    {
        match *step {
            ProofStep::AtClause {
                redundant,
                clause,
                propagation_hashes,
            } => {
                self.lit_buf.clear();
                self.lit_buf.extend(clause.iter().cloned().map(map_lit));
                self.hash_buf.clear();
                self.hash_buf
                    .extend(propagation_hashes.iter().cloned().map(map_hash));
                ProofStep::AtClause {
                    redundant,
                    clause: &self.lit_buf,
                    propagation_hashes: &self.hash_buf,
                }
            }

            ProofStep::UnitClauses(units) => {
                self.unit_buf.clear();
                self.unit_buf.extend(
                    units
                        .iter()
                        .map(|&(lit, hash)| (map_lit(lit), map_hash(hash))),
                );
                ProofStep::UnitClauses(&self.unit_buf)
            }

            ProofStep::DeleteClause { clause, proof } => {
                self.lit_buf.clear();
                self.lit_buf.extend(clause.iter().cloned().map(map_lit));
                ProofStep::DeleteClause {
                    clause: &self.lit_buf,
                    proof,
                }
            }

            ProofStep::Model(model) => {
                self.lit_buf.clear();
                self.lit_buf.extend(model.iter().cloned().map(map_lit));
                ProofStep::Model(&self.lit_buf)
            }

            ProofStep::ChangeHashBits(..) | ProofStep::End => step.clone(),
        }
    }
}
