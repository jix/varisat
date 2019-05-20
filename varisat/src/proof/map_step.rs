//! Maps literals and hashes of clause steps between the solver and the checker.

use varisat_formula::{Lit, Var};

use super::{ClauseHash, ProofStep};

/// Maps literals and hashes of clause steps between the solver and the checker.
#[derive(Default)]
pub struct MapStep {
    lit_buf: Vec<Lit>,
    hash_buf: Vec<ClauseHash>,
    unit_buf: Vec<(Lit, ClauseHash)>,
}

impl MapStep {
    pub fn map_lits(&mut self, lits: &[Lit], map_var: impl Fn(Var) -> Var) -> &[Lit] {
        let map_var_ref = &map_var;
        self.lit_buf.clear();
        self.lit_buf
            .extend(lits.iter().map(|lit| lit.map_var(map_var_ref)));
        &self.lit_buf
    }

    pub fn map<'s, 'a, 'b>(
        &'a mut self,
        step: &ProofStep<'b>,
        map_var: impl Fn(Var) -> Var,
        map_hash: impl Fn(ClauseHash) -> ClauseHash,
    ) -> ProofStep<'s>
    where
        'a: 's,
        'b: 's,
    {
        let map_var_ref = &map_var;
        let map_lit = |lit: Lit| lit.map_var(map_var_ref);
        match *step {
            ProofStep::AddClause { clause } => {
                self.lit_buf.clear();
                self.lit_buf.extend(clause.iter().cloned().map(map_lit));
                ProofStep::AddClause {
                    clause: &self.lit_buf,
                }
            }

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

            ProofStep::Assumptions(assumptions) => {
                self.lit_buf.clear();
                self.lit_buf
                    .extend(assumptions.iter().cloned().map(map_lit));
                ProofStep::Assumptions(&self.lit_buf)
            }

            ProofStep::FailedAssumptions {
                failed_core,
                propagation_hashes,
            } => {
                self.lit_buf.clear();
                self.lit_buf
                    .extend(failed_core.iter().cloned().map(map_lit));
                self.hash_buf.clear();
                self.hash_buf
                    .extend(propagation_hashes.iter().cloned().map(map_hash));
                ProofStep::FailedAssumptions {
                    failed_core: &self.lit_buf,
                    propagation_hashes: &self.hash_buf,
                }
            }

            ProofStep::ChangeHashBits(..) | ProofStep::End => step.clone(),

            ProofStep::SolverVarNames { .. } => {
                // while this step does contain variables, it is used to update the mapping, so it
                // shouldn't be mapped itself.
                step.clone()
            }
        }
    }
}
