//! Temporary data.
use crate::lit::Lit;

/// Temporary data used by various parts of the solver.
///
/// Make sure to check any documented invariants when using this. Also make sure to check all
/// existing users when adding invariants.
#[derive(Default)]
pub struct TmpData {
    pub lits: Vec<Lit>,
}
