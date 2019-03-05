use partial_ref::{partial, PartialRef};

use crate::context::{AssignmentP, Context, ImplGraphP, TrailP};
use crate::lit::{Lit, LitIdx};

use super::Reason;

/// Current partial assignment.
#[derive(Default)]
pub struct Assignment {
    assignment: Vec<Option<bool>>,
}

impl Assignment {
    /// Update structures for a new variable count.
    pub fn set_var_count(&mut self, count: usize) {
        self.assignment.resize(count, None);
    }

    /// Current partial assignment as slice.
    pub fn assignment(&self) -> &[Option<bool>] {
        &self.assignment
    }

    pub fn lit_value(&self, lit: Lit) -> Option<bool> {
        self.assignment[lit.index()].map(|b| b ^ lit.is_negative())
    }

    pub fn lit_is_true(&self, lit: Lit) -> bool {
        self.assignment[lit.index()] == Some(lit.is_positive())
    }

    pub fn lit_is_false(&self, lit: Lit) -> bool {
        self.assignment[lit.index()] == Some(lit.is_negative())
    }

    pub fn assign_lit(&mut self, lit: Lit) {
        self.assignment[lit.index()] = lit.is_positive().into()
    }
}

/// Decision and propagation history.
#[derive(Default)]
pub struct Trail {
    /// Stack of all propagated and all enqueued assignments
    trail: Vec<Lit>,
    /// Next assignment in trail to propagate
    queue_head_pos: usize,
    /// Decision levels as trail indices.
    decisions: Vec<LitIdx>,
}

impl Trail {
    /// Return the next assigned literal to propagate.
    pub fn queue_head(&self) -> Option<Lit> {
        self.trail.get(self.queue_head_pos).cloned()
    }

    pub fn pop_queue(&mut self) {
        self.queue_head_pos += 1;
        debug_assert!(self.queue_head_pos <= self.trail.len());
    }

    /// Assigned literals in assignment order.
    pub fn trail(&self) -> &[Lit] {
        &self.trail
    }

    /// Start a new decision level.
    ///
    /// Does not enqueue the decision itself.
    pub fn new_decision_level(&mut self) {
        self.decisions.push(self.trail.len() as LitIdx)
    }

    /// Current decision level.
    pub fn current_level(&self) -> usize {
        self.decisions.len()
    }
}

/// Enqueues the assignment of true to a literal.
///
/// This updates the assignment and trail, but does not perform any propagation. The literal has to
/// be unassigned when calling this.
pub fn enqueue_assignment(
    mut ctx: partial!(Context, mut AssignmentP, mut ImplGraphP, mut TrailP),
    lit: Lit,
    reason: Reason,
) {
    let assignment = ctx.part_mut(AssignmentP);
    debug_assert!(assignment.lit_value(lit) == None);

    assignment.assign_lit(lit);

    let (trail, mut ctx) = ctx.split_part_mut(TrailP);

    trail.trail.push(lit);

    let node = &mut ctx.part_mut(ImplGraphP).nodes[lit.index()];
    node.reason = reason;
    node.level = trail.decisions.len() as LitIdx;
}

/// Undo all assignments in decision levels deeper than the given level.
pub fn backtrack(mut ctx: partial!(Context, mut AssignmentP, mut TrailP), level: usize) {
    let (assignment, mut ctx) = ctx.split_part_mut(AssignmentP);
    let trail = ctx.part_mut(TrailP);

    if level == trail.decisions.len() {
        return;
    }

    let new_trail_len = trail.decisions[level] as usize;

    trail.queue_head_pos = new_trail_len;
    trail.decisions.truncate(level);

    let trail_end = &trail.trail[new_trail_len..];
    for &lit in trail_end {
        assignment.assignment[lit.index()] = None;
        // TODO phase saving
    }
    trail.trail.truncate(new_trail_len);
}
