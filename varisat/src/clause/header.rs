//! Metadata stored in the header of each long clause.
use std::cmp::min;

use crate::lit::{LitIdx, Var};

use super::Tier;

/// Length of a [`ClauseHeader`] in multiples of [`LitIdx`]
pub(super) const HEADER_LEN: usize = 3;

const TIER_WORD: usize = HEADER_LEN - 2;
const TIER_OFFSET: usize = 0;
const TIER_MASK: LitIdx = 0b11;

const DELETED_WORD: usize = HEADER_LEN - 2;
const DELETED_OFFSET: usize = 2;

const MARK_WORD: usize = HEADER_LEN - 2;
const MARK_OFFSET: usize = 3;

const GLUE_WORD: usize = HEADER_LEN - 2;
const GLUE_OFFSET: usize = 4;
const GLUE_MASK: LitIdx = (1 << 6) - 1;

const ACTIVE_WORD: usize = HEADER_LEN - 2;
const ACTIVE_OFFSET: usize = 10;

const ACTIVITY_WORD: usize = HEADER_LEN - 3;

/// Metadata for a clause.
///
/// This is stored in a [`ClauseAlloc`](super::ClauseAlloc) and thus must have a representation
/// compatible with slice of [`LitIdx`] values.
#[repr(transparent)]
#[derive(Copy, Clone, Default)]
pub struct ClauseHeader {
    pub(super) data: [LitIdx; HEADER_LEN],
}

impl ClauseHeader {
    /// Create a new clause header with default entries.
    pub fn new() -> ClauseHeader {
        Self::default()
    }

    /// Length of the clause.
    pub fn len(&self) -> usize {
        self.data[HEADER_LEN - 1] as usize
    }

    /// Set the length of the clause.
    ///
    /// Must be `<= Var::max_count()` as each variable may only be present once per clause.
    pub fn set_len(&mut self, length: usize) {
        debug_assert!(length <= Var::max_count());

        self.data[HEADER_LEN - 1] = length as LitIdx;
    }

    /// Whether the clause is marked as deleted.
    pub fn deleted(&self) -> bool {
        (self.data[DELETED_WORD] >> DELETED_OFFSET) & 1 != 0
    }

    /// Mark the clause as deleted.
    pub fn set_deleted(&mut self, deleted: bool) {
        let word = &mut self.data[DELETED_WORD];
        *word = (*word & !(1 << DELETED_OFFSET)) | ((deleted as LitIdx) << DELETED_OFFSET);
    }

    /// Current [`Tier`] of the clause.
    pub fn tier(&self) -> Tier {
        unsafe { Tier::from_index(((self.data[TIER_WORD] >> TIER_OFFSET) & TIER_MASK) as usize) }
    }

    /// Set the current [`Tier`] of the clause.
    pub fn set_tier(&mut self, tier: Tier) {
        let word = &mut self.data[TIER_WORD];
        *word = (*word & !(TIER_MASK << TIER_OFFSET)) | ((tier as LitIdx) << TIER_OFFSET);
    }

    /// Whether the clause is redundant.
    pub fn redundant(&self) -> bool {
        self.tier() != Tier::Irred
    }

    /// Whether the clause is marked.
    ///
    /// The mark is a temporary bit that can be set by various routines, but should always be reset
    /// to false.
    pub fn mark(&self) -> bool {
        (self.data[MARK_WORD] >> MARK_OFFSET) & 1 != 0
    }

    /// Mark or unmark the clause.
    ///
    /// Make sure to clear the mark after use.
    pub fn set_mark(&mut self, mark: bool) {
        let word = &mut self.data[MARK_WORD];
        *word = (*word & !(1 << MARK_OFFSET)) | ((mark as LitIdx) << MARK_OFFSET);
    }

    /// The clause's active flag
    ///
    /// This is set when a clause was involved in conflict analysis and periodically reset.
    pub fn active(&self) -> bool {
        (self.data[ACTIVE_WORD] >> ACTIVE_OFFSET) & 1 != 0
    }

    /// Set or reset the clause's active flag.
    pub fn set_active(&mut self, active: bool) {
        let word = &mut self.data[ACTIVE_WORD];
        *word = (*word & !(1 << ACTIVE_OFFSET)) | ((active as LitIdx) << ACTIVE_OFFSET);
    }

    /// The [glue][crate::glue] level.
    pub fn glue(&self) -> usize {
        ((self.data[GLUE_WORD] >> GLUE_OFFSET) & GLUE_MASK) as usize
    }

    /// Update the [glue][crate::glue] level.
    pub fn set_glue(&mut self, glue: usize) {
        let glue = min(glue, GLUE_MASK as usize) as LitIdx;
        let word = &mut self.data[GLUE_WORD];

        *word = (*word & !(GLUE_MASK << GLUE_OFFSET)) | (glue << GLUE_OFFSET);
    }

    /// Clause [activity][crate::clause::activity].
    pub fn activity(&self) -> f32 {
        f32::from_bits(self.data[ACTIVITY_WORD] as u32)
    }

    /// Update clause [activity][crate::clause::activity].
    pub fn set_activity(&mut self, activity: f32) {
        self.data[ACTIVITY_WORD] = activity.to_bits() as LitIdx;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tier_mask() {
        assert!(Tier::count() <= TIER_MASK as usize + 1);
    }
}
