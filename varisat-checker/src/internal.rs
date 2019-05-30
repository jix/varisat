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
        self.ctx.checker_state.step += 1;
        self.ctx.checker_state.check_step(step)
    }

    fn self_check_delayed_steps(&mut self) -> Result<(), CheckerError> {
        self.ctx.checker_state.process_unit_conflicts()
    }
}
