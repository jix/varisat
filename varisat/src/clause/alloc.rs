//! Clause allocator.
use std::mem::transmute;
use std::slice;

use crate::lit::{Lit, LitIdx};

use super::{Clause, ClauseHeader, HEADER_LEN};

/// Integer type used to store offsets into [`ClauseAlloc`]'s memory.
type ClauseOffset = u32;

/// Bump allocator for clause storage.
///
/// Clauses are allocated from a single continuous buffer. Clauses cannot be freed individually. To
/// reclaim space from deleted clauses, a new `ClauseAlloc` is created and the remaining clauses are
/// copied over.
///
/// When the `ClauseAlloc`'s buffer is full, it is reallocated using the growing strategy of
/// [`Vec`]. External references ([`ClauseRef`]) store an offset into the `ClauseAlloc`'s memory and
/// remaind valid when the buffer is grown. Clauses are aligned and the offset represents a multiple
/// of the alignment size. This allows using 32-bit offsets while still supporting up to 16GB of
/// clauses.
///
/// **Safety**: Using the safe methods is always memory safe, even if invariants of the clause
/// storage are violated. An example invariant is using only ClauseRef's produced by the same
/// ClauseAlloc. Some places in this codebase use the unsafe methods and expect users of the safe
/// methods to not violate these invariants. It is important that this does not leak through the
/// public API, i.e. crate external code using safe methods must be unable to violate invariants
/// expected for internal unsafe code.
#[derive(Default)]
pub struct ClauseAlloc {
    buffer: Vec<LitIdx>,
}

impl ClauseAlloc {
    /// Create an emtpy clause allocator.
    pub fn new() -> ClauseAlloc {
        ClauseAlloc::default()
    }

    /// Create a clause allocator with preallocated capacity.
    pub fn with_capacity(capacity: usize) -> ClauseAlloc {
        ClauseAlloc {
            buffer: Vec::with_capacity(capacity),
        }
    }

    /// Allocate space for and add a new clause.
    ///
    /// Clauses have a minimal size of 3, as binary and unit clauses are handled separately. This is
    /// enforced on the ClauseAlloc level to safely avoid extra bound checks when accessing the
    /// initial literals of a clause.
    ///
    /// The size of the header will be set to the size of the given slice. The returned
    /// [`ClauseRef`] can be used to access the new clause.
    pub fn add_clause(&mut self, mut header: ClauseHeader, lits: &[Lit]) -> ClauseRef {
        let offset = self.buffer.len();

        assert!(
            lits.len() >= 3,
            "ClauseAlloc can only store ternary and larger clauses"
        );

        // TODO Maybe let the caller handle this?
        assert!(
            offset <= (ClauseOffset::max_value() as usize),
            "Exceeded ClauseAlloc's maximal buffer size"
        );

        header.set_len(lits.len());

        self.buffer.extend_from_slice(&header.data);

        let lit_idx_slice = unsafe {
            // This is safe as Lit and LitIdx have the same representation
            slice::from_raw_parts(lits.as_ptr() as *const LitIdx, lits.len())
        };

        self.buffer.extend_from_slice(lit_idx_slice);

        ClauseRef {
            offset: offset as ClauseOffset,
        }
    }

    /// Access the header of a clause.
    pub fn header(&self, cref: ClauseRef) -> &ClauseHeader {
        let offset = cref.offset as usize;
        assert!(
            offset as usize + HEADER_LEN <= self.buffer.len(),
            "ClauseRef out of bounds"
        );
        unsafe { self.header_unchecked(cref) }
    }

    /// Mutate the header of a clause.
    pub fn header_mut(&mut self, cref: ClauseRef) -> &mut ClauseHeader {
        let offset = cref.offset as usize;
        assert!(
            offset as usize + HEADER_LEN <= self.buffer.len(),
            "ClauseRef out of bounds"
        );
        unsafe { self.header_unchecked_mut(cref) }
    }

    unsafe fn header_unchecked(&self, cref: ClauseRef) -> &ClauseHeader {
        let offset = cref.offset as usize;
        let header_pointer = self.buffer.as_ptr().add(offset) as *const ClauseHeader;
        &*header_pointer
    }

    unsafe fn header_unchecked_mut(&mut self, cref: ClauseRef) -> &mut ClauseHeader {
        let offset = cref.offset as usize;
        let header_pointer = self.buffer.as_mut_ptr().add(offset) as *mut ClauseHeader;
        &mut *header_pointer
    }

    /// Access a clause.
    pub fn clause(&self, cref: ClauseRef) -> &Clause {
        let header = self.header(cref);
        let len = header.len();

        let lit_offset = cref.offset as usize + HEADER_LEN;
        let lit_end = lit_offset + len;
        assert!(lit_end <= self.buffer.len(), "ClauseRef out of bounds");
        unsafe { self.clause_with_len_unchecked(cref, len) }
    }

    /// Mutate a clause.
    pub fn clause_mut(&mut self, cref: ClauseRef) -> &mut Clause {
        let header = self.header(cref);
        let len = header.len();

        let lit_offset = cref.offset as usize + HEADER_LEN;
        let lit_end = lit_offset + len;
        assert!(lit_end <= self.buffer.len(), "ClauseRef out of bounds");
        unsafe { self.clause_with_len_unchecked_mut(cref, len) }
    }

    unsafe fn clause_with_len_unchecked(&self, cref: ClauseRef, len: usize) -> &Clause {
        let offset = cref.offset as usize;
        transmute::<&[LitIdx], &Clause>(slice::from_raw_parts(
            self.buffer.as_ptr().add(offset),
            len + HEADER_LEN,
        ))
    }

    unsafe fn clause_with_len_unchecked_mut(&mut self, cref: ClauseRef, len: usize) -> &mut Clause {
        let offset = cref.offset as usize;
        transmute::<&mut [LitIdx], &mut Clause>(slice::from_raw_parts_mut(
            self.buffer.as_mut_ptr().add(offset),
            len + HEADER_LEN,
        ))
    }

    /// Current buffer size in multiples of [`LitIdx`].
    pub fn buffer_size(&self) -> usize {
        self.buffer.len()
    }
}

/// Compact reference to a clause.
///
/// Used with [`ClauseAlloc`] to access the clause.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct ClauseRef {
    offset: ClauseOffset,
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::cnf::{strategy::*, CnfFormula};

    use proptest::*;

    proptest! {
        #[test]
        fn roundtrip_from_cnf_formula(input in cnf_formula(1..100usize, 0..1000, 3..30)) {

            let mut clause_alloc = ClauseAlloc::new();
            let mut clause_refs = vec![];

            for clause_lits in input.iter() {
                let header = ClauseHeader::new();
                clause_refs.push(clause_alloc.add_clause(header, clause_lits));
            }

            let mut recovered = CnfFormula::new();

            for cref in clause_refs {
                let clause = clause_alloc.clause(cref);
                prop_assert_eq!(clause.header().len(), clause.lits().len());
                recovered.add_clause(clause.lits());
            }

            // Ignore difference caused by unused vars
            recovered.set_var_count(input.var_count());

            prop_assert_eq!(input, recovered);
        }

        #[test]
        fn clause_mutation(input in cnf_formula(1..100usize, 0..1000, 3..30)) {

            let mut clause_alloc = ClauseAlloc::new();
            let mut clause_refs = vec![];

            for clause_lits in input.iter() {
                let header = ClauseHeader::new();
                clause_refs.push(clause_alloc.add_clause(header, clause_lits));
            }

            for &cref in clause_refs.iter() {
                let clause = clause_alloc.clause_mut(cref);
                clause.lits_mut().reverse();
            }

            for &cref in clause_refs.iter() {
                let clause_len = clause_alloc.clause(cref).lits().len();
                if clause_len > 3 {
                    clause_alloc.header_mut(cref).set_len(clause_len - 1);
                }
            }

            for (&cref, lits) in clause_refs.iter().zip(input.iter()) {
                let expected = if lits.len() > 3 {
                    lits[1..].iter().rev()
                } else {
                    lits.iter().rev()
                };
                prop_assert!(clause_alloc.clause(cref).lits().iter().eq(expected));
            }
        }
    }
}
