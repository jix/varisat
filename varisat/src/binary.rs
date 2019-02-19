//! Binary clauses.

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
