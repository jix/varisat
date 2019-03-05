//! Decision heuristics.

use partial_ref::{partial, PartialRef};

use crate::context::{AssignmentP, Context, ImplGraphP, TrailP};
use crate::lit::{Lit, Var};
use crate::prop::{enqueue_assignment, Reason};

/// Make a decision and enqueue it.
///
/// This is a dummy decision heuristic for now.
///
/// Returns `false` if no decision was made because all variables are assigned.
pub fn make_decision(
    mut ctx: partial!(Context, mut AssignmentP, mut ImplGraphP, mut TrailP),
) -> bool {
    if let Some(index) = ctx
        .part(AssignmentP)
        .assignment()
        .iter()
        .position(|value| value.is_none())
    {
        let decision_var = Var::from_index(index);

        let decision = Lit::from_var(decision_var, false);

        ctx.part_mut(TrailP).new_decision_level();

        enqueue_assignment(ctx.borrow(), decision, Reason::Unit);

        true
    } else {
        false
    }
}
