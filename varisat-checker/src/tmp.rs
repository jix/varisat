//! Temporary data.
use varisat_formula::Lit;

#[derive(Default)]
pub struct TmpData {
    /// Temporary storage for literals.
    pub tmp: Vec<Lit>,
}
