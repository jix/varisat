//! Clause storage (unit and non-unit clauses).
use std::{convert::TryInto, mem::transmute};

use partial_ref::{partial, PartialRef};
use rustc_hash::FxHashMap as HashMap;
use smallvec::SmallVec;

use varisat_formula::{lit::LitIdx, Lit};
use varisat_internal_proof::ClauseHash;

use crate::{
    context::{parts::*, Context},
    processing::{process_step, CheckedProofStep},
    sorted_lits::copy_canonical,
    variables::{ensure_sampling_var, ensure_var},
    CheckerError,
};

const INLINE_LITS: usize = 3;

/// Literals of a clause, either inline or an index into a buffer
pub struct ClauseLits {
    length: LitIdx,
    inline: [LitIdx; INLINE_LITS],
}

impl ClauseLits {
    /// Create a new ClauseLits, storing them in the given buffer if necessary
    fn new(lits: &[Lit], buffer: &mut Vec<Lit>) -> ClauseLits {
        let mut inline = [0; INLINE_LITS];
        let length = lits.len();

        if length > INLINE_LITS {
            inline[0] = buffer
                .len()
                .try_into()
                .expect("exceeded maximal literal buffer size");
            buffer.extend(lits);
        } else {
            let lits = unsafe {
                // Lit is a repr(transparent) wrapper of LitIdx
                #[allow(clippy::transmute_ptr_to_ptr)]
                transmute::<&[Lit], &[LitIdx]>(lits)
            };
            inline[..length].copy_from_slice(lits);
        }

        ClauseLits {
            length: length as LitIdx,
            inline,
        }
    }

    /// Returns the literals as a slice given a storage buffer
    pub fn slice<'a, 'b, 'c>(&'a self, buffer: &'b [Lit]) -> &'c [Lit]
    where
        'a: 'c,
        'b: 'c,
    {
        if self.length > INLINE_LITS as LitIdx {
            &buffer[self.inline[0] as usize..][..self.length as usize]
        } else {
            unsafe {
                // Lit is a repr(transparent) wrapper of LitIdx
                #[allow(clippy::transmute_ptr_to_ptr)]
                transmute::<&[LitIdx], &[Lit]>(&self.inline[..self.length as usize])
            }
        }
    }

    /// Literals stored in the literal buffer
    fn buffer_used(&self) -> usize {
        if self.length > INLINE_LITS as LitIdx {
            self.length as usize
        } else {
            0
        }
    }
}

/// Literals and metadata for non-unit clauses.
pub struct Clause {
    /// LRAT clause id.
    pub id: u64,
    /// How often the clause is present as irred., red. clause.
    ///
    /// For checking the formula is a multiset of clauses. This is necessary as the generating
    /// solver might not check for duplicated clauses.
    ref_count: [u32; 2],
    /// Clause's literals.
    pub lits: ClauseLits,
}

/// Identifies the origin of a unit clause.
#[derive(Copy, Clone, Debug)]
pub enum UnitId {
    Global(u64),
    TracePos(usize),
    InClause,
}

/// Known unit clauses and metadata.
#[derive(Copy, Clone, Debug)]
pub struct UnitClause {
    pub id: UnitId,
    pub value: bool,
}

/// Return type of [`store_clause`]
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum StoreClauseResult {
    New,
    Duplicate,
    NewlyIrredundant,
}

/// Return type of [`delete_clause`]
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum DeleteClauseResult {
    Unchanged,
    NewlyRedundant,
    Removed,
}
/// Checker clause storage.
#[derive(Default)]
pub struct Clauses {
    /// Next clause id to use.
    pub next_clause_id: u64,
    /// Literal storage for clauses,
    pub literal_buffer: Vec<Lit>,
    /// Number of literals in the buffer which are from deleted clauses.
    garbage_size: usize,
    /// Stores all known non-unit clauses indexed by their hash.
    pub clauses: HashMap<ClauseHash, SmallVec<[Clause; 1]>>,
    /// Stores known unit clauses and propagations during a clause check.
    pub unit_clauses: Vec<Option<UnitClause>>,
    /// This stores a conflict of input unit clauses.
    ///
    /// Our representation for unit clauses doesn't support conflicting units so this is used as a
    /// workaround.
    pub unit_conflict: Option<[u64; 2]>,
}

impl Clauses {
    /// Value of a literal if known from unit clauses.
    pub fn lit_value(&self, lit: Lit) -> Option<(bool, UnitClause)> {
        self.unit_clauses[lit.index()]
            .map(|unit_clause| (unit_clause.value ^ lit.is_negative(), unit_clause))
    }
}

/// Adds a clause to the checker.
pub fn add_clause<'a>(
    mut ctx: partial!(Context<'a>, mut ClausesP, mut CheckerStateP, mut ProcessingP<'a>, mut TmpDataP, mut VariablesP, ClauseHasherP),
    clause: &[Lit],
) -> Result<(), CheckerError> {
    if ctx.part(CheckerStateP).unsat {
        return Ok(());
    }

    let (tmp_data, mut ctx) = ctx.split_part_mut(TmpDataP);

    if copy_canonical(&mut tmp_data.tmp, clause) {
        let (clauses, mut ctx) = ctx.split_part_mut(ClausesP);
        process_step(
            ctx.borrow(),
            &CheckedProofStep::TautologicalClause {
                id: clauses.next_clause_id,
                clause: &tmp_data.tmp,
            },
        )?;
        clauses.next_clause_id += 1;
        return Ok(());
    }

    for &lit in tmp_data.tmp.iter() {
        ensure_sampling_var(ctx.borrow(), lit.var())?;
    }

    let (id, added) = store_clause(ctx.borrow(), &tmp_data.tmp, false);

    let (clauses, mut ctx) = ctx.split_part_mut(ClausesP);

    match added {
        StoreClauseResult::New => {
            process_step(
                ctx.borrow(),
                &CheckedProofStep::AddClause {
                    id,
                    clause: &tmp_data.tmp,
                },
            )?;
        }
        StoreClauseResult::NewlyIrredundant | StoreClauseResult::Duplicate => {
            if let StoreClauseResult::NewlyIrredundant = added {
                process_step(
                    ctx.borrow(),
                    &CheckedProofStep::MakeIrredundant {
                        id,
                        clause: &tmp_data.tmp,
                    },
                )?;
            }

            process_step(
                ctx.borrow(),
                &CheckedProofStep::DuplicatedClause {
                    id: clauses.next_clause_id,
                    same_as_id: id,
                    clause: &tmp_data.tmp,
                },
            )?;
            // This is a duplicated clause. We want to ensure that the clause ids match the input
            // order so we skip a clause id.
            clauses.next_clause_id += 1;
        }
    }

    Ok(())
}

/// Adds a clause to the checker data structures.
///
/// `lits` must be sorted and free of duplicates.
///
/// Returns the id of the added clause and indicates whether the clause is new or changed from
/// redundant to irredundant.
pub fn store_clause(
    mut ctx: partial!(
        Context,
        mut CheckerStateP,
        mut ClausesP,
        mut VariablesP,
        ClauseHasherP
    ),
    lits: &[Lit],
    redundant: bool,
) -> (u64, StoreClauseResult) {
    for &lit in lits.iter() {
        ensure_var(ctx.borrow(), lit.var());
    }

    match lits[..] {
        [] => {
            let id = ctx.part(ClausesP).next_clause_id;
            ctx.part_mut(ClausesP).next_clause_id += 1;

            ctx.part_mut(CheckerStateP).unsat = true;
            (id, StoreClauseResult::New)
        }
        [lit] => store_unit_clause(ctx.borrow(), lit),
        _ => {
            let hash = ctx.part(ClauseHasherP).clause_hash(&lits);

            let (clauses, mut ctx) = ctx.split_part_mut(ClausesP);

            let candidates = clauses.clauses.entry(hash).or_default();

            for candidate in candidates.iter_mut() {
                if candidate.lits.slice(&clauses.literal_buffer) == &lits[..] {
                    let result = if !redundant && candidate.ref_count[0] == 0 {
                        // first irredundant copy
                        StoreClauseResult::NewlyIrredundant
                    } else {
                        StoreClauseResult::Duplicate
                    };

                    let ref_count = &mut candidate.ref_count[redundant as usize];
                    *ref_count = ref_count.checked_add(1).expect("ref_count overflow");
                    return (candidate.id, result);
                }
            }

            let id = clauses.next_clause_id;

            let mut ref_count = [0, 0];
            ref_count[redundant as usize] += 1;

            candidates.push(Clause {
                id,
                ref_count,
                lits: ClauseLits::new(&lits, &mut clauses.literal_buffer),
            });

            clauses.next_clause_id += 1;

            for &lit in lits.iter() {
                ctx.part_mut(VariablesP).lit_data[lit.code()].clause_count += 1;
            }

            (id, StoreClauseResult::New)
        }
    }
}

/// Adds a unit clause to the checker data structures.
///
/// Returns the id of the added clause and a boolean that is true if the clause wasn't already
/// present.
pub fn store_unit_clause(
    mut ctx: partial!(Context, mut CheckerStateP, mut ClausesP),
    lit: Lit,
) -> (u64, StoreClauseResult) {
    match ctx.part(ClausesP).lit_value(lit) {
        Some((
            true,
            UnitClause {
                id: UnitId::Global(id),
                ..
            },
        )) => (id, StoreClauseResult::Duplicate),
        Some((
            false,
            UnitClause {
                id: UnitId::Global(conflicting_id),
                ..
            },
        )) => {
            ctx.part_mut(CheckerStateP).unsat = true;
            let id = ctx.part(ClausesP).next_clause_id;
            ctx.part_mut(ClausesP).unit_conflict = Some([conflicting_id, id]);
            ctx.part_mut(ClausesP).next_clause_id += 1;
            (id, StoreClauseResult::New)
        }
        Some(_) => unreachable!(),
        None => {
            let id = ctx.part(ClausesP).next_clause_id;

            ctx.part_mut(ClausesP).unit_clauses[lit.index()] = Some(UnitClause {
                value: lit.is_positive(),
                id: UnitId::Global(id),
            });

            ctx.part_mut(ClausesP).next_clause_id += 1;

            (id, StoreClauseResult::New)
        }
    }
}

/// Delete a clause from the current formula.
///
/// `lits` must be sorted and free of duplicates.
///
/// Returns the id of the deleted clause and whether the ref_count (or irredundant ref_count)
/// became zero.
pub fn delete_clause(
    mut ctx: partial!(
        Context,
        mut ClausesP,
        mut VariablesP,
        CheckerStateP,
        ClauseHasherP
    ),
    lits: &[Lit],
    redundant: bool,
) -> Result<(u64, DeleteClauseResult), CheckerError> {
    if lits.len() < 2 {
        return Err(CheckerError::check_failed(
            ctx.part(CheckerStateP).step,
            format!("delete of unit or empty clause {:?}", lits),
        ));
    }

    let hash = ctx.part(ClauseHasherP).clause_hash(lits);

    let clauses = ctx.part_mut(ClausesP);

    let candidates = clauses.clauses.entry(hash).or_default();

    let mut found = false;

    let mut result = None;

    let literal_buffer = &clauses.literal_buffer;
    let garbage_size = &mut clauses.garbage_size;

    candidates.retain(|candidate| {
        if found || candidate.lits.slice(literal_buffer) != lits {
            true
        } else {
            found = true;
            let ref_count = &mut candidate.ref_count[redundant as usize];

            if *ref_count == 0 {
                true
            } else {
                *ref_count -= 1;

                if candidate.ref_count == [0, 0] {
                    *garbage_size += candidate.lits.buffer_used();
                    result = Some((candidate.id, DeleteClauseResult::Removed));
                    false
                } else {
                    if !redundant && candidate.ref_count[0] == 0 {
                        result = Some((candidate.id, DeleteClauseResult::NewlyRedundant));
                    } else {
                        result = Some((candidate.id, DeleteClauseResult::Unchanged));
                    }
                    true
                }
            }
        }
    });

    if candidates.is_empty() {
        clauses.clauses.remove(&hash);
    }

    if let Some((_, DeleteClauseResult::Removed)) = result {
        for &lit in lits.iter() {
            ctx.part_mut(VariablesP).lit_data[lit.code()].clause_count -= 1;
        }
    }

    if let Some(result) = result {
        collect_garbage(ctx.borrow());
        return Ok(result);
    }

    let msg = match (found, redundant) {
        (false, _) => format!("delete of unknown clause {:?}", lits),
        (_, true) => format!("delete of redundant clause {:?} which is irredundant", lits),
        (_, false) => format!("delete of irredundant clause {:?} which is redundant", lits),
    };
    Err(CheckerError::check_failed(
        ctx.part(CheckerStateP).step,
        msg,
    ))
}

/// Perform a garbage collection if required
fn collect_garbage(mut ctx: partial!(Context, mut ClausesP)) {
    let clauses = ctx.part_mut(ClausesP);
    if clauses.garbage_size * 2 <= clauses.literal_buffer.len() {
        return;
    }

    let mut new_buffer = vec![];

    new_buffer.reserve(clauses.literal_buffer.len());

    for (_, candidates) in clauses.clauses.iter_mut() {
        for clause in candidates.iter_mut() {
            let new_lits =
                ClauseLits::new(clause.lits.slice(&clauses.literal_buffer), &mut new_buffer);
            clause.lits = new_lits;
        }
    }

    clauses.literal_buffer = new_buffer;
    clauses.garbage_size = 0;
}
