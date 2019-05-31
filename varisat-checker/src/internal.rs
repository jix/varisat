//! Varisat internal interface used for on-the-fly checking.

use partial_ref::{IntoPartialRefMut, PartialRef};

use varisat_internal_proof::ProofStep;

use crate::state::{check_step, process_unit_conflicts};
use crate::{Checker, CheckerError};

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
        let mut ctx = self.ctx.into_partial_ref_mut();
        check_step(ctx.borrow(), step)
    }

    fn self_check_delayed_steps(&mut self) -> Result<(), CheckerError> {
        let mut ctx = self.ctx.into_partial_ref_mut();
        process_unit_conflicts(ctx.borrow())
    }
}
