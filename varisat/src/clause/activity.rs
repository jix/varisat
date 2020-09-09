//! Clause activity.
use partial_ref::{partial, PartialRef};

use crate::{
    config::SolverConfig,
    context::{parts::*, Context},
};

use super::ClauseRef;

/// Clause activity.
///
/// The individual clause activities are stored in the clause allocator. This stores global metadata
/// used for bumping and decaying activities.
pub struct ClauseActivity {
    /// The value to add on bumping.
    bump: f32,
    /// The inverse of the decay factor.
    inv_decay: f32,
}

impl Default for ClauseActivity {
    fn default() -> ClauseActivity {
        ClauseActivity {
            bump: 1.0,
            inv_decay: 1.0 / SolverConfig::default().clause_activity_decay,
        }
    }
}

impl ClauseActivity {
    /// Change the decay factor.
    pub fn set_decay(&mut self, decay: f32) {
        assert!(decay < 1.0);
        assert!(decay > 1.0 / 16.0);
        self.inv_decay = 1.0 / decay;
    }
}

/// Rescale activities if any value exceeds this value.
fn rescale_limit() -> f32 {
    std::f32::MAX / 16.0
}

/// Increase a clause's activity.
pub fn bump_clause_activity(
    mut ctx: partial!(
        Context,
        mut ClauseActivityP,
        mut ClauseAllocP,
        mut ClauseDbP,
    ),
    cref: ClauseRef,
) {
    let bump = ctx.part(ClauseActivityP).bump;
    let header = ctx.part_mut(ClauseAllocP).header_mut(cref);

    let activity = header.activity() + bump;

    header.set_activity(activity);

    if activity > rescale_limit() {
        rescale_clause_activities(ctx.borrow());
    }
}

/// Rescale all values to avoid an overflow.
fn rescale_clause_activities(
    mut ctx: partial!(
        Context,
        mut ClauseActivityP,
        mut ClauseAllocP,
        mut ClauseDbP,
    ),
) {
    let rescale_factor = 1.0 / rescale_limit();

    let (db, mut ctx) = ctx.split_part_mut(ClauseDbP);
    let (alloc, mut ctx) = ctx.split_part_mut(ClauseAllocP);
    db.clauses.retain(|&cref| {
        let header = alloc.header_mut(cref);
        if header.deleted() {
            false
        } else {
            let activity = header.activity() * rescale_factor;
            header.set_activity(activity);
            true
        }
    });
    ctx.part_mut(ClauseActivityP).bump *= rescale_factor;
}

/// Decay the clause activities.
pub fn decay_clause_activities(
    mut ctx: partial!(
        Context,
        mut ClauseActivityP,
        mut ClauseAllocP,
        mut ClauseDbP,
    ),
) {
    let activities = ctx.part_mut(ClauseActivityP);
    activities.bump *= activities.inv_decay;
    if activities.bump >= rescale_limit() {
        rescale_clause_activities(ctx.borrow());
    }
}
