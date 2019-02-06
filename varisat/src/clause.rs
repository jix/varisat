//! Clause storage.
use std::slice;

use crate::lit::{Lit, LitIdx, Var};

pub mod alloc;

pub use alloc::ClauseAlloc;

/// Length of a [`ClauseHeader`] in multiples of [`LitIdx`]
const HEADER_LEN: usize = 1;

/// Metadata for a clause.
///
/// This is stored in a [`ClauseAlloc`] and thus must have a representation compatible with slice of
/// [`LitIdx`] values.
#[repr(transparent)]
pub struct ClauseHeader {
    data: [LitIdx; HEADER_LEN],
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
}

impl Default for ClauseHeader {
    fn default() -> ClauseHeader {
        let length = 0;

        ClauseHeader {
            data: [length as LitIdx],
        }
    }
}

/// A clause.
///
/// This is stoed in a [`ClauseAlloc`] and thus must have a representation compatible with slice of
/// [`LitIdx`] values.
///
/// It would be nicer to use a DST struct with two members and `repr(C)`, but while that can be
/// declared in stable rust, it's almost impossible to work with.
#[repr(transparent)]
pub struct Clause {
    data: [LitIdx],
}

impl Clause {
    /// The clause's header
    pub fn header(&self) -> &ClauseHeader {
        unsafe {
            let header_ptr = self.data.as_ptr() as *const ClauseHeader;
            &*header_ptr
        }
    }

    /// Mutable reference to the clause's header
    pub fn header_mut(&mut self) -> &mut ClauseHeader {
        unsafe {
            let header_ptr = self.data.as_mut_ptr() as *mut ClauseHeader;
            &mut *header_ptr
        }
    }

    /// The clause's literals
    pub fn lits(&self) -> &[Lit] {
        unsafe {
            let lit_ptr = self.data.as_ptr().add(HEADER_LEN) as *const Lit;
            slice::from_raw_parts(lit_ptr, self.data.len() - HEADER_LEN)
        }
    }

    /// Mutable slice of the clause's literals
    pub fn lits_mut(&mut self) -> &mut [Lit] {
        unsafe {
            let lit_ptr = self.data.as_mut_ptr().add(HEADER_LEN) as *mut Lit;
            slice::from_raw_parts_mut(lit_ptr, self.data.len() - HEADER_LEN)
        }
    }
}
