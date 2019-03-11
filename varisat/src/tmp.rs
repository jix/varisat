//! Temporary data.
use crate::lit::Lit;

/// Temporary data used by various parts of the solver.
///
/// Make sure to check any documented invariants when using this. Also make sure to check all
/// existing users when adding invariants.
#[derive(Default)]
pub struct TmpData {
    pub lits: Vec<Lit>,
    /// A boolean for each literal.
    ///
    /// Reset to all-false, keep size.
    pub flags: Vec<bool>,
}

impl TmpData {
    /// Update structures for a new variable count.
    pub fn set_var_count(&mut self, count: usize) {
        self.flags.resize(count * 2, false);
    }
}
