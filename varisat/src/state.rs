//! Miscellaneous solver state.
use crate::solver::SolverError;

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
pub struct SolverState {
    pub sat_state: SatState,
    pub formula_is_empty: bool,
    pub state_is_invalid: bool,
    pub solver_error: Option<SolverError>,
}

impl Default for SolverState {
    fn default() -> SolverState {
        SolverState {
            sat_state: SatState::Unknown,
            formula_is_empty: true,
            state_is_invalid: false,
            solver_error: None,
        }
    }
}
