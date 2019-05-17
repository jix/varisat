//! Varisat internal interface used for on-the-fly checking.

use varisat_internal_proof::ProofStep;

use super::{Checker, CheckerError};

/// Varisat internal interface used for on-the-fly checking.
///
/// This should only be used within other Varisat crates. It is not considered part of the public
/// API and may change at any time.
pub trait SelfChecker {
    fn self_check_step(&mut self, step: ProofStep) -> Result<(), CheckerError>;

    fn self_check_delayed_steps(&mut self) -> Result<(), CheckerError>;
}

impl<'a> SelfChecker for Checker<'a> {
    fn self_check_step(&mut self, step: ProofStep) -> Result<(), CheckerError> {
        self.check_step(step)
    }

    fn self_check_delayed_steps(&mut self) -> Result<(), CheckerError> {
        self.process_unit_conflicts()
    }
}
