//! Computation of clause hashes.
use std::mem::replace;

use hashbrown::HashMap;
use partial_ref::{partial, PartialRef};

use varisat_formula::{Lit, Var};
use varisat_internal_proof::{lit_code_hash, lit_hash, ClauseHash};

use crate::context::{parts::*, Context};

pub struct ClauseHasher {
    /// How many bits are used for storing clause hashes.
    pub hash_bits: u32,
    /// Changed solver names that are not yet reflected in the checkers current clause hashes.
    pub buffered_solver_var_names: Vec<(Var, Option<Var>)>,
    /// Does buffered_solver_var_names contain a new name?
    ///
    /// If it contains only deletes, there is no need to rehash
    pub rename_in_buffered_solver_var_names: bool,
    /// Current mapping from global var names to solver var names, used for hashing.
    solver_var_names: HashMap<Var, Var>,
}

impl Default for ClauseHasher {
    fn default() -> ClauseHasher {
        ClauseHasher {
            hash_bits: 64,
            buffered_solver_var_names: vec![],
            rename_in_buffered_solver_var_names: false,
            solver_var_names: Default::default(),
        }
    }
}

impl ClauseHasher {
    /// Compute a clause hash of the current bit size
    pub fn clause_hash(&self, lits: &[Lit]) -> ClauseHash {
        let shift_bits = ClauseHash::max_value().count_ones() - self.hash_bits;
        let mut hash = 0;
        for &lit in lits.iter() {
            match self.solver_var_names.get(&lit.var()) {
                Some(var) => hash ^= lit_hash(var.lit(lit.is_positive())),
                None => hash ^= lit_code_hash(lit.code() + Var::max_count() * 2),
            }
        }
        hash >> shift_bits
    }
}

/// Recompute all clause hashes if necessary
pub fn rehash(mut ctx: partial!(Context, mut ClauseHasherP, mut ClausesP)) {
    let (hasher, mut ctx) = ctx.split_part_mut(ClauseHasherP);
    let clauses = ctx.part_mut(ClausesP);

    for (global, solver) in hasher.buffered_solver_var_names.drain(..) {
        if let Some(solver) = solver {
            hasher.solver_var_names.insert(global, solver);
        } else {
            hasher.solver_var_names.remove(&global);
        }
    }
    hasher.rename_in_buffered_solver_var_names = false;

    let mut old_clauses = replace(&mut clauses.clauses, Default::default());

    for (_, mut candidates) in old_clauses.drain() {
        for clause in candidates.drain() {
            let hash = hasher.clause_hash(clause.lits.slice(&clauses.literal_buffer));
            let candidates = clauses.clauses.entry(hash).or_default();
            candidates.push(clause);
        }
    }
}
