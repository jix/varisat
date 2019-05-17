//! Decision heuristics.

use partial_ref::{partial, PartialRef};

use varisat_formula::{Lit, Var};

use crate::context::{parts::*, Context};
use crate::prop::{enqueue_assignment, Reason};

pub mod vsids;

/// Make a decision and enqueue it.
///
/// Returns `false` if no decision was made because all variables are assigned.
pub fn make_decision(
    mut ctx: partial!(
        Context,
        mut AssignmentP,
        mut ImplGraphP,
        mut TrailP,
        mut VsidsP
    ),
) -> bool {
    let (vsids, mut ctx) = ctx.split_part_mut(VsidsP);

    if let Some(decision_var) = vsids
        .filter(|&var| ctx.part(AssignmentP).var_value(var).is_none())
        .next()
    {
        let decision = Lit::from_var(
            decision_var,
            !ctx.part(AssignmentP).last_var_value(decision_var),
        );

        ctx.part_mut(TrailP).new_decision_level();

        enqueue_assignment(ctx.borrow(), decision, Reason::Unit);

        true
    } else {
        false
    }
}

/// Make a variable available for decisions.
pub fn make_available(mut ctx: partial!(Context, mut VsidsP), var: Var) {
    ctx.part_mut(VsidsP).make_available(var);
}
