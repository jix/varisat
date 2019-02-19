//! Miscellaneous solver state.

/// Satisfiability state.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum SatState {
    Unknown,
    Sat,
    Unsat,
    UnsatUnderAssumptions,
}

impl Default for SatState {
    fn default() -> SatState {
        SatState::Unknown
    }
}

/// Miscellaneous solver state.
///
/// Anything larger or any larger group of related state variables should be moved into a separate
/// part of [`Context`](crate::context::Context).
#[derive(Default)]
pub struct SolverState {
    pub sat_state: SatState,
}
