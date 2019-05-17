//! Propagation of binary clauses.
use partial_ref::{partial, PartialRef};

use varisat_formula::Lit;

use crate::context::{AssignmentP, BinaryClausesP, Context, ImplGraphP, TrailP};

use super::enqueue_assignment;
use super::{Conflict, Reason};

/// Propagate all literals implied by the given literal via binary clauses.
///
/// On conflict return the binary clause propgating the conflicting assignment.
pub fn propagate_binary(
    mut ctx: partial!(
        Context,
        mut AssignmentP,
        mut ImplGraphP,
        mut TrailP,
        BinaryClausesP,
    ),
    lit: Lit,
) -> Result<(), Conflict> {
    let (binary_clauses, mut ctx) = ctx.split_part(BinaryClausesP);

    for &implied in binary_clauses.implied(lit) {
        let assignment = ctx.part(AssignmentP);

        if assignment.lit_is_false(implied) {
            return Err(Conflict::Binary([implied, !lit]));
        } else if !assignment.lit_is_true(implied) {
            enqueue_assignment(ctx.borrow(), implied, Reason::Binary([!lit]));
        }
    }

    Ok(())
}
