//! Metadata stored in the header of each long clause.
use crate::lit::{LitIdx, Var};

use super::Tier;

/// Length of a [`ClauseHeader`] in multiples of [`LitIdx`]
pub(super) const HEADER_LEN: usize = 2;

const TIER_WORD: usize = HEADER_LEN - 2;
const TIER_OFFSET: usize = 0;
const TIER_MASK: u32 = 0b11;

const DELETED_WORD: usize = HEADER_LEN - 2;
const DELETED_OFFSET: usize = 2;

/// Metadata for a clause.
///
/// This is stored in a [`ClauseAlloc`](super::ClauseAlloc) and thus must have a representation
/// compatible with slice of [`LitIdx`] values.
#[repr(transparent)]
#[derive(Default)]
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
        *word = (*word & !(TIER_MASK << TIER_OFFSET)) | ((tier as u32) << TIER_OFFSET);
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
