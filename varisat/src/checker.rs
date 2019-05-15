//! Check unsatisfiability proofs.

use std::convert::TryInto;
use std::io;
use std::mem::{replace, transmute};
use std::ops::Range;

use failure::{Error, Fail};
use hashbrown::{HashMap, HashSet};
use smallvec::SmallVec;

use crate::cnf::CnfFormula;
use crate::dimacs::DimacsParser;
use crate::lit::{Lit, LitIdx};
use crate::proof::{clause_hash, varisat::Parser, ClauseHash, DeleteClauseProof, ProofStep};

mod write_lrat;

pub use write_lrat::WriteLrat;

/// Possible errors while checking a varisat proof.
#[derive(Debug, Fail)]
pub enum CheckerError {
    #[fail(
        display = "step {}: Proof ended without deriving unsatisfiability",
        step
    )]
    ProofIncomplete { step: u64 },
    #[fail(display = "step {}: Error reading proof file: {}", step, cause)]
    IoError {
        step: u64,
        #[cause]
        cause: io::Error,
    },
    #[fail(display = "step {}: Could not parse proof step: {}", step, cause)]
    ParseError {
        step: u64,
        #[cause]
        cause: Error,
    },
    #[fail(display = "step {}: Checking proof failed: {}", step, msg)]
    CheckFailed {
        step: u64,
        msg: String,
        debug_step: String,
    },
    #[fail(display = "Error in proof processor: {}", cause)]
    ProofProcessorError {
        #[cause]
        cause: Error,
    },
    #[doc(hidden)]
    #[fail(display = "__Nonexhaustive")]
    __Nonexhaustive,
}

impl CheckerError {
    /// Generate a CheckFailed error with an empty debug_step
    fn check_failed(step: u64, msg: String) -> CheckerError {
        CheckerError::CheckFailed {
            step,
            msg,
            debug_step: String::new(),
        }
    }
}

/// A single step of a proof.
///
/// Clauses are identified by a unique increasing id assigned by the checker. Whenever the literals
/// of a clause are included in a step, they are sorted and free of duplicates.
#[derive(Debug)]
pub enum CheckedProofStep<'a> {
    /// A clause of the input formula.
    AddClause { id: u64, clause: &'a [Lit] },
    /// A duplicated clause of the input formula.
    ///
    /// The checker detects duplicated clauses and will use the same id for all copies. This also
    /// applies to clauses of the input formula. This step allows proof processors to identify the
    /// input formula's clauses by consecutive ids. When a duplicate clause is found, an id is
    /// allocated and this step is emitted. The duplicated clause is not considered part of the
    /// formula and the allocated id will not be used in any other steps.
    DuplicatedClause {
        id: u64,
        same_as_id: u64,
        clause: &'a [Lit],
    },
    /// Addition of an asymmetric tautology (AT).
    ///
    /// A clause C is an asymmetric tautology wrt. a formula F, iff unit propagation in F with the
    /// negated literals of C as unit clauses leads to a conflict. The `propagations` field contains
    /// clauses in the order they became unit and as last element the clause that caused a conflict.
    AtClause {
        id: u64,
        redundant: bool,
        clause: &'a [Lit],
        propagations: &'a [u64],
    },
    /// Deletion of a redundant clause.
    DeleteClause { id: u64, clause: &'a [Lit] },
    /// Deletion of a clause that is an asymmetric tautology w.r.t the remaining irredundant
    /// clauses.
    DeleteAtClause {
        id: u64,
        keep_as_redundant: bool,
        clause: &'a [Lit],
        propagations: &'a [u64],
    },
    /// Make a redundant clause irredundant.
    MakeIrredundant { id: u64, clause: &'a [Lit] },
    /// A (partial) assignment that satisfies all clauses.
    Model { assignment: &'a [Lit] },
}

/// Implement to process proof steps.
pub trait ProofProcessor {
    fn process_step(&mut self, step: &CheckedProofStep) -> Result<(), Error>;
}

const INLINE_LITS: usize = 3;

/// Literals of a clause, either inline or an index into a buffer
struct ClauseLits {
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
    fn slice<'a, 'b, 'c>(&'a self, buffer: &'b [Lit]) -> &'c [Lit]
    where
        'a: 'c,
        'b: 'c,
    {
        if self.length > INLINE_LITS as LitIdx {
            &buffer[self.inline[0] as usize..][..self.length as usize]
        } else {
            unsafe {
                // Lit is a repr(transparent) wrapper of LitIdx
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
struct Clause {
    /// LRAT clause id.
    id: u64,
    /// How often the clause is present as irred., red. clause.
    ///
    /// For checking the formula is a multiset of clauses. This is necessary as the generating
    /// solver might not check for duplicated clauses.
    ref_count: [u32; 2],
    /// Clause's literals.
    lits: ClauseLits,
}

/// Identifies the origin of a unit clause.
#[derive(Copy, Clone)]
enum UnitId {
    Global(u64),
    TracePos(usize),
    InClause,
}

/// Known unit clauses and metadata.
#[derive(Copy, Clone)]
struct UnitClause {
    id: UnitId,
    value: bool,
}

/// Propagation of the RUP check.
struct TraceItem {
    id: u64,
    edges: Range<usize>,
    unused: bool,
}

/// Return type of [`Checker::store_clause`]
#[derive(Copy, Clone, PartialEq, Eq)]
enum StoreClauseResult {
    New,
    Duplicate,
    NewlyIrredundant,
}

/// Return type of [`Checker::delete_clause`]
#[derive(Copy, Clone, PartialEq, Eq)]
enum DeleteClauseResult {
    Unchanged,
    NewlyRedundant,
    Removed,
}

/// A checker for unsatisfiability proofs in the native varisat format.
pub struct Checker<'a> {
    /// Current step number.
    step: u64,
    /// Next clause id to use.
    next_clause_id: u64,
    /// Literal storage for clauses,
    literal_buffer: Vec<Lit>,
    /// Number of literals in the buffer which are from deleted clauses.
    garbage_size: usize,
    /// Stores all known non-unit clauses indexed by their hash.
    clauses: HashMap<ClauseHash, SmallVec<[Clause; 1]>>,
    /// Stores known unit clauses and propagations during a clause check.
    unit_clauses: Vec<Option<UnitClause>>,
    /// Stores overwritten values in `unit_clauses` to undo assignments.
    trail: Vec<(Lit, Option<UnitClause>)>,
    /// Whether unsatisfiability was proven.
    unsat: bool,
    /// Involved clauses during the last check.
    trace: Vec<TraceItem>,
    /// Edges of the trace implication graph.
    trace_edges: Vec<LitIdx>,
    /// Just the ids of `trace`.
    trace_ids: Vec<u64>,
    /// Registered proof processors.
    processors: Vec<&'a mut dyn ProofProcessor>,
    /// This stores a conflict of input unit clauses.
    ///
    /// Our representation for unit clauses doesn't support conflicting units so this is used as a
    /// workaround.
    unit_conflict: Option<[u64; 2]>,
    /// Temporary storage for literals.
    tmp: Vec<Lit>,
    /// How many bits are used for storing clause hashes.
    hash_bits: u32,
    /// Last added irredundant clause id.
    ///
    /// Sorted and free of duplicates.
    previous_irred_clause_id: Option<u64>,
    /// Last added irredundant clause literals.
    previous_irred_clause_lits: Vec<Lit>,
}

impl<'a> Default for Checker<'a> {
    fn default() -> Checker<'a> {
        Checker {
            step: 0,
            next_clause_id: 0,
            literal_buffer: vec![],
            garbage_size: 0,
            clauses: Default::default(),
            unit_clauses: vec![],
            trail: vec![],
            unsat: false,
            trace: vec![],
            trace_edges: vec![],
            trace_ids: vec![],
            processors: vec![],
            unit_conflict: None,
            tmp: vec![],
            hash_bits: 64,
            previous_irred_clause_id: None,
            previous_irred_clause_lits: vec![],
        }
    }
}

impl<'a> Checker<'a> {
    /// Create a new checker.
    pub fn new() -> Checker<'a> {
        Checker::default()
    }

    /// Add a formula to the checker.
    pub fn add_formula(&mut self, formula: &CnfFormula) -> Result<(), CheckerError> {
        for clause in formula.iter() {
            self.add_clause(clause)?;
        }

        Ok(())
    }

    /// Adds a clause to the checker.
    pub fn add_clause(&mut self, clause: &[Lit]) -> Result<(), CheckerError> {
        if self.unsat {
            return Ok(());
        }

        let mut tmp = replace(&mut self.tmp, vec![]);
        tmp.clear();
        tmp.extend_from_slice(&clause);

        tmp.sort_unstable();
        tmp.dedup();

        let (id, added) = self.store_clause(&tmp, false);

        self.tmp = tmp;

        match added {
            StoreClauseResult::New => {
                Self::process_step(
                    &mut self.processors,
                    &CheckedProofStep::AddClause {
                        id: id,
                        clause: &self.tmp,
                    },
                )?;
            }
            StoreClauseResult::NewlyIrredundant | StoreClauseResult::Duplicate => {
                if let StoreClauseResult::NewlyIrredundant = added {
                    Self::process_step(
                        &mut self.processors,
                        &CheckedProofStep::MakeIrredundant {
                            id,
                            clause: &self.tmp,
                        },
                    )?;
                }

                Self::process_step(
                    &mut self.processors,
                    &CheckedProofStep::DuplicatedClause {
                        id: self.next_clause_id,
                        same_as_id: id,
                        clause: &self.tmp,
                    },
                )?;
                // This is a duplicated clause. We want to ensure that the clause ids match the input
                // order so we skip a clause id.
                self.next_clause_id += 1;
            }
        }

        Ok(())
    }

    /// Reads and adds a formula in DIMACS CNF format.
    ///
    /// Using this avoids creating a temporary [`CnfFormula`].
    pub fn add_dimacs_cnf(&mut self, input: impl io::Read) -> Result<(), Error> {
        let parser = DimacsParser::parse_incremental(input, |parser| {
            Ok(self.add_formula(&parser.take_formula())?)
        })?;

        log::info!(
            "Parsed formula with {} variables and {} clauses",
            parser.var_count(),
            parser.clause_count()
        );

        Ok(())
    }

    /// Compute a clause hash of the current bit size
    fn clause_hash(&self, lits: &[Lit]) -> ClauseHash {
        let shift_bits = ClauseHash::max_value().count_ones() - self.hash_bits;
        clause_hash(lits) >> shift_bits
    }

    /// Value of a literal if known from unit clauses.
    fn lit_value(&self, lit: Lit) -> Option<(bool, UnitClause)> {
        self.unit_clauses
            .get(lit.index())
            .and_then(|&value| value)
            .map(|unit_clause| (unit_clause.value ^ lit.is_negative(), unit_clause))
    }

    /// Adds a clause to the checker data structures.
    ///
    /// `lits` must be sorted and free of duplicates.
    ///
    /// Returns the id of the added clause and indicates whether the clause is new or changed from
    /// redundant to irredundant.
    fn store_clause(&mut self, lits: &[Lit], redundant: bool) -> (u64, StoreClauseResult) {
        match lits[..] {
            [] => {
                let id = self.next_clause_id;
                self.next_clause_id += 1;

                self.unsat = true;
                (id, StoreClauseResult::New)
            }
            [lit] => self.store_unit_clause(lit),
            _ => {
                let hash = self.clause_hash(&lits);

                let candidates = self.clauses.entry(hash).or_default();

                for candidate in candidates.iter_mut() {
                    if candidate.lits.slice(&self.literal_buffer) == &lits[..] {
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

                let id = self.next_clause_id;

                let mut ref_count = [0, 0];
                ref_count[redundant as usize] += 1;

                candidates.push(Clause {
                    id,
                    ref_count,
                    lits: ClauseLits::new(&lits, &mut self.literal_buffer),
                });

                self.next_clause_id += 1;
                (id, StoreClauseResult::New)
            }
        }
    }

    /// Adds a unit clause to the checker data structures.
    ///
    /// Returns the id of the added clause and a boolean that is true if the clause wasn't already
    /// present.
    fn store_unit_clause(&mut self, lit: Lit) -> (u64, StoreClauseResult) {
        match self.lit_value(lit) {
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
                self.unsat = true;
                let id = self.next_clause_id;
                self.unit_conflict = Some([conflicting_id, id]);
                self.next_clause_id += 1;
                (id, StoreClauseResult::New)
            }
            Some(_) => unreachable!(),
            None => {
                if self.unit_clauses.len() <= lit.index() {
                    self.unit_clauses.resize(lit.index() + 1, None);
                }

                let id = self.next_clause_id;

                self.unit_clauses[lit.index()] = Some(UnitClause {
                    value: lit.is_positive(),
                    id: UnitId::Global(id),
                });

                self.next_clause_id += 1;

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
    fn delete_clause(
        &mut self,
        lits: &[Lit],
        redundant: bool,
    ) -> Result<(u64, DeleteClauseResult), CheckerError> {
        if lits.len() < 2 {
            return Err(CheckerError::check_failed(
                self.step,
                format!("delete of unit or empty clause {:?}", lits),
            ));
        }

        let hash = self.clause_hash(lits);

        let candidates = self.clauses.entry(hash).or_default();

        let mut found = false;

        let mut result = None;

        let literal_buffer = &self.literal_buffer;
        let garbage_size = &mut self.garbage_size;

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
            self.clauses.remove(&hash);
        }

        if let Some(result) = result {
            self.collect_garbage();
            return Ok(result);
        }

        let msg = match (found, redundant) {
            (false, _) => format!("delete of unknown clause {:?}", lits),
            (_, true) => format!("delete of redundant clause {:?} which is irredundant", lits),
            (_, false) => format!("delete of irredundant clause {:?} which is redundant", lits),
        };
        return Err(CheckerError::check_failed(self.step, msg));
    }

    /// Perform a garbage collection if required
    fn collect_garbage(&mut self) {
        if self.garbage_size * 2 <= self.literal_buffer.len() {
            return;
        }

        let mut new_buffer = vec![];

        new_buffer.reserve(self.literal_buffer.len());

        for (_, candidates) in self.clauses.iter_mut() {
            for clause in candidates.iter_mut() {
                let new_lits =
                    ClauseLits::new(clause.lits.slice(&self.literal_buffer), &mut new_buffer);
                clause.lits = new_lits;
            }
        }

        self.literal_buffer = new_buffer;
        self.garbage_size = 0;
    }

    /// Recompute all clause hashes
    fn rehash(&mut self) {
        let mut old_clauses = replace(&mut self.clauses, Default::default());

        for (_, mut candidates) in old_clauses.drain() {
            for clause in candidates.drain() {
                let hash = self.clause_hash(clause.lits.slice(&self.literal_buffer));
                let candidates = self.clauses.entry(hash).or_default();
                candidates.push(clause);
            }
        }
    }

    /// Check whether a clause is implied by clauses of the given hashes.
    ///
    /// `lits` must be sorted and free of duplicates.
    fn check_clause_with_hashes(
        &mut self,
        lits: &[Lit],
        propagation_hashes: &[ClauseHash],
    ) -> Result<(), CheckerError> {
        self.trace.clear();
        self.trace_edges.clear();

        let mut rup_is_unsat = false;

        assert!(self.trail.is_empty());

        // Set all lits to false
        for &lit in lits.iter() {
            if self.unit_clauses.len() <= lit.index() {
                self.unit_clauses.resize(lit.index() + 1, None);
            }

            self.trail.push((lit, self.unit_clauses[lit.index()]));

            self.unit_clauses[lit.index()] = Some(UnitClause {
                value: lit.is_negative(),
                id: UnitId::InClause,
            });
        }

        'hashes: for &hash in propagation_hashes.iter() {
            let candidates = match self.clauses.get(&hash) {
                Some(candidates) if !candidates.is_empty() => candidates,
                _ => {
                    return Err(CheckerError::check_failed(
                        self.step,
                        format!("no clause found for hash {:x}", hash),
                    ))
                }
            };

            // Check if any clause matching the hash propagates
            'candidates: for clause in candidates.iter() {
                let mut unassigned_count = 0;
                let mut unassigned_lit = None;

                let range_begin = self.trace_edges.len();

                for &lit in clause.lits.slice(&self.literal_buffer).iter() {
                    match self.lit_value(lit) {
                        Some((true, _)) => {
                            continue 'candidates;
                        }
                        Some((false, unit)) => match unit.id {
                            UnitId::Global(id) => {
                                self.trail.push((lit, self.unit_clauses[lit.index()]));
                                self.unit_clauses[lit.index()] = Some(UnitClause {
                                    value: lit.is_negative(),
                                    id: UnitId::TracePos(self.trace.len()),
                                });

                                self.trace_edges.push(self.trace.len() as LitIdx);

                                self.trace.push(TraceItem {
                                    id,
                                    edges: 0..0,
                                    unused: true,
                                });
                            }
                            UnitId::TracePos(pos) => {
                                self.trace_edges.push(pos as LitIdx);
                            }
                            UnitId::InClause => {}
                        },
                        None => {
                            unassigned_count += 1;
                            unassigned_lit = Some(lit);
                        }
                    }
                }

                let range = range_begin..self.trace_edges.len();

                match unassigned_lit {
                    None => {
                        self.trace.push(TraceItem {
                            id: clause.id,
                            edges: range,
                            unused: false,
                        });

                        rup_is_unsat = true;
                        break 'hashes;
                    }
                    Some(lit) if unassigned_count == 1 => {
                        if self.unit_clauses.len() <= lit.index() {
                            self.unit_clauses.resize(lit.index() + 1, None);
                        }

                        self.trail.push((lit, self.unit_clauses[lit.index()]));

                        self.unit_clauses[lit.index()] = Some(UnitClause {
                            value: lit.is_positive(),
                            id: UnitId::TracePos(self.trace.len()),
                        });

                        self.trace.push(TraceItem {
                            id: clause.id,
                            edges: range,
                            unused: true,
                        });
                    }
                    _ => (),
                }
            }
        }

        if rup_is_unsat && !self.processors.is_empty() {
            for i in (0..self.trace.len()).rev() {
                if !self.trace[i].unused {
                    let edges = self.trace[i].edges.clone();
                    for &edge in self.trace_edges[edges].iter() {
                        self.trace[edge as usize].unused = false;
                    }
                }
            }
            self.trace_ids.clear();
            self.trace_ids
                .extend(self.trace.iter().map(|trace| trace.id));
        }

        // Undo temporary assignments
        for (lit, value) in self.trail.drain(..).rev() {
            self.unit_clauses[lit.index()] = value;
        }

        if rup_is_unsat {
            Ok(())
        } else {
            Err(CheckerError::check_failed(
                self.step,
                format!("AT check failed for {:?}", lits),
            ))
        }
    }

    /// Check whether a given clause is subsumed by the last added irredundant clause.
    ///
    /// `lits` must be sorted and free of duplicates.
    fn subsumed_by_previous_irred_clause(&self, lits: &[Lit]) -> bool {
        if self.previous_irred_clause_id.is_none() {
            return false;
        }
        let mut subset = &self.previous_irred_clause_lits[..];
        let mut superset = lits;

        let mut strict = false;

        while let Some((&sub_min, sub_rest)) = subset.split_first() {
            if let Some((&super_min, super_rest)) = superset.split_first() {
                if sub_min < super_min {
                    // sub_min is not in superset
                    return false;
                } else if sub_min > super_min {
                    // super_min is not in subset, skip it
                    superset = super_rest;
                    strict = true;
                } else {
                    // sub_min == super_min, go to next element
                    superset = super_rest;
                    subset = sub_rest;
                }
            } else {
                // sub_min is not in superset
                return false;
            }
        }
        strict |= !superset.is_empty();
        strict
    }

    /// Check a single proof step
    pub(crate) fn check_step(&mut self, step: ProofStep) -> Result<(), CheckerError> {
        let mut result = match step {
            ProofStep::AtClause {
                redundant,
                clause,
                propagation_hashes,
            } => self.check_at_clause_step(redundant, clause, propagation_hashes),
            ProofStep::DeleteClause { clause, proof } => {
                self.check_delete_clause_step(clause, proof)
            }
            ProofStep::UnitClauses(units) => self.check_unit_clauses_step(units),
            ProofStep::ChangeHashBits(bits) => {
                self.hash_bits = bits;
                self.rehash();
                Ok(())
            }
            ProofStep::Model(model) => self.check_model_step(model),
        };

        if let Err(CheckerError::CheckFailed {
            ref mut debug_step, ..
        }) = result
        {
            *debug_step = format!("{:?}", step)
        }
        result
    }

    /// Check an AtClause step
    fn check_at_clause_step(
        &mut self,
        redundant: bool,
        clause: &[Lit],
        propagation_hashes: &[ClauseHash],
    ) -> Result<(), CheckerError> {
        let mut tmp = replace(&mut self.tmp, vec![]);
        tmp.clear();
        tmp.extend_from_slice(&clause);

        tmp.sort_unstable();
        tmp.dedup();

        self.check_clause_with_hashes(&tmp, &*propagation_hashes)?;

        let (id, added) = self.store_clause(&tmp, redundant);

        if !redundant {
            self.previous_irred_clause_id = Some(id);
            self.previous_irred_clause_lits.clear();
            self.previous_irred_clause_lits.extend_from_slice(&tmp);
        }

        match added {
            StoreClauseResult::New => {
                Self::process_step(
                    &mut self.processors,
                    &CheckedProofStep::AtClause {
                        id,
                        redundant: redundant,
                        clause: &tmp,
                        propagations: &self.trace_ids,
                    },
                )?;
            }
            StoreClauseResult::NewlyIrredundant => {
                Self::process_step(
                    &mut self.processors,
                    &CheckedProofStep::MakeIrredundant { id, clause: &tmp },
                )?;
            }
            StoreClauseResult::Duplicate => (),
        }

        self.tmp = tmp;

        Ok(())
    }

    /// Check a DeleteClause step
    fn check_delete_clause_step(
        &mut self,
        clause: &[Lit],
        proof: DeleteClauseProof,
    ) -> Result<(), CheckerError> {
        let mut tmp = replace(&mut self.tmp, vec![]);
        tmp.clear();
        tmp.extend_from_slice(&clause);

        tmp.sort_unstable();
        tmp.dedup();

        let redundant = proof == DeleteClauseProof::Redundant;

        let mut subsumed_by = None;

        match proof {
            DeleteClauseProof::Redundant => (),
            DeleteClauseProof::Satisfied => {
                if !tmp.iter().any(|&lit| {
                    if let Some((
                        true,
                        UnitClause {
                            id: UnitId::Global(id),
                            ..
                        },
                    )) = self.lit_value(lit)
                    {
                        subsumed_by = Some(id);
                        true
                    } else {
                        false
                    }
                }) {
                    return Err(CheckerError::check_failed(
                        self.step,
                        format!("deleted clause {:?} is not satisfied", clause),
                    ));
                }
            }
            DeleteClauseProof::Simplified => {
                subsumed_by = self.previous_irred_clause_id;
                if !self.subsumed_by_previous_irred_clause(&tmp) {
                    return Err(CheckerError::check_failed(
                        self.step,
                        format!(
                            "deleted clause {:?} is not subsumed by previous clause {:?}",
                            clause, self.previous_irred_clause_lits
                        ),
                    ));
                }
            }
        }

        self.previous_irred_clause_id = None;
        self.previous_irred_clause_lits.clear();

        let (id, deleted) = self.delete_clause(&tmp, redundant)?;

        if redundant {
            match deleted {
                DeleteClauseResult::Removed => {
                    Self::process_step(
                        &mut self.processors,
                        &CheckedProofStep::DeleteClause {
                            id: id,
                            clause: &tmp,
                        },
                    )?;
                }
                DeleteClauseResult::Unchanged => (),
                DeleteClauseResult::NewlyRedundant => unreachable!(),
            }
        } else {
            match deleted {
                DeleteClauseResult::Removed | DeleteClauseResult::NewlyRedundant => {
                    Self::process_step(
                        &mut self.processors,
                        &CheckedProofStep::DeleteAtClause {
                            id: id,
                            keep_as_redundant: deleted == DeleteClauseResult::NewlyRedundant,
                            clause: &tmp,
                            propagations: &[subsumed_by.unwrap()],
                        },
                    )?;
                }
                DeleteClauseResult::Unchanged => (),
            }
        }

        self.tmp = tmp;
        Ok(())
    }

    /// Check a UnitClauses step
    fn check_unit_clauses_step(&mut self, units: &[(Lit, ClauseHash)]) -> Result<(), CheckerError> {
        for &(lit, hash) in units.iter() {
            let clause = [lit];
            let propagation_hashes = [hash];
            self.check_clause_with_hashes(&clause[..], &propagation_hashes[..])?;

            let (id, added) = self.store_unit_clause(lit);

            match added {
                StoreClauseResult::New => {
                    Self::process_step(
                        &mut self.processors,
                        &CheckedProofStep::AtClause {
                            id,
                            redundant: false,
                            clause: &clause,
                            propagations: &self.trace_ids,
                        },
                    )?;
                }
                StoreClauseResult::Duplicate => (),
                StoreClauseResult::NewlyIrredundant => unreachable!(),
            }
        }
        Ok(())
    }

    /// Check a Model step
    fn check_model_step(&mut self, model: &[Lit]) -> Result<(), CheckerError> {
        let mut assignments = HashSet::new();

        for &lit in model.iter() {
            if let Some((false, _)) = self.lit_value(lit) {
                return Err(CheckerError::check_failed(
                    self.step,
                    format!("model assignment conflicts with unit clause {:?}", !lit),
                ));
            }
            if assignments.contains(&!lit) {
                return Err(CheckerError::check_failed(
                    self.step,
                    format!("model contains conflicting assignment {:?}", !lit),
                ));
            }
            assignments.insert(lit);
        }

        for (_, candidates) in self.clauses.iter() {
            for clause in candidates.iter() {
                let lits = clause.lits.slice(&self.literal_buffer);
                if !lits.iter().any(|lit| assignments.contains(&lit)) {
                    return Err(CheckerError::check_failed(
                        self.step,
                        format!("model does not satisfy clause {:?}", lits),
                    ));
                }
            }
        }
        Ok(())
    }

    /// Invoke all proof processors for a CheckedProofStep
    fn process_step<'b>(
        processors: &'b mut [&'a mut dyn ProofProcessor],
        step: &CheckedProofStep<'b>,
    ) -> Result<(), CheckerError> {
        for processor in processors.iter_mut() {
            if let Err(err) = processor.process_step(step) {
                return Err(CheckerError::ProofProcessorError { cause: err });
            }
        }

        Ok(())
    }

    /// Reads and adds a formula in DIMACS CNF format.
    ///
    /// Using this avoids creating a temporary [`CnfFormula`].
    pub fn check_proof(&mut self, input: impl io::Read) -> Result<(), CheckerError> {
        let mut buffer = io::BufReader::new(input);
        let mut parser = Parser::default();

        while !self.unsat {
            self.step += 1;

            if self.step % 100000 == 0 {
                log::info!("checking step {}k", self.step / 1000);
            }

            match parser.parse_step(&mut buffer) {
                Ok(step) => self.check_step(step)?,
                Err(err) => match err.downcast::<io::Error>() {
                    Ok(io_err) => {
                        if io_err.kind() == io::ErrorKind::UnexpectedEof {
                            return Err(CheckerError::ProofIncomplete { step: self.step });
                        } else {
                            return Err(CheckerError::IoError {
                                step: self.step,
                                cause: io_err,
                            });
                        }
                    }
                    Err(err) => {
                        return Err(CheckerError::ParseError {
                            step: self.step,
                            cause: err.into(),
                        })
                    }
                },
            }
        }

        self.process_unit_conflicts()
    }

    /// Process unit conflicts detected during clause loading.
    pub(crate) fn process_unit_conflicts(&mut self) -> Result<(), CheckerError> {
        if let Some(ids) = &self.unit_conflict {
            let clause = &[];
            Self::process_step(
                &mut self.processors,
                &CheckedProofStep::AtClause {
                    id: self.next_clause_id,
                    redundant: false,
                    clause,
                    propagations: ids,
                },
            )?;
        }

        Ok(())
    }

    /// Add a [`ProofProcessor`].
    ///
    /// This has to be called before loading any clauses or checking any proofs.
    pub fn add_processor(&mut self, processor: &'a mut dyn ProofProcessor) {
        self.processors.push(processor);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;

    use crate::dimacs::write_dimacs;

    use crate::test::sgen_unsat_formula;

    use crate::solver::{ProofFormat, Solver};

    fn expect_check_failed(result: Result<(), CheckerError>, contains: &str) {
        match result {
            Err(CheckerError::CheckFailed { ref msg, .. }) if msg.contains(contains) => (),
            err => panic!("expected {:?} error but got {:?}", contains, err),
        }
    }

    #[test]
    fn conflicting_units() {
        let mut checker = Checker::new();

        checker
            .add_formula(&cnf_formula![
                1;
                -1;
            ])
            .unwrap();

        assert!(checker.unsat);
    }

    #[test]
    fn invalid_delete() {
        let mut checker = Checker::new();

        checker
            .add_formula(&cnf_formula![
                1, 2, 3;
                -4, 5;
            ])
            .unwrap();

        expect_check_failed(
            checker.check_step(ProofStep::DeleteClause {
                clause: &lits![-5, 4],
                proof: DeleteClauseProof::Redundant,
            }),
            "unknown clause",
        );
    }

    #[test]
    fn ref_counts() {
        let mut checker = Checker::new();

        checker
            .add_formula(&cnf_formula![
                1, 2, 3;
                1, 2, 3;
                1;
            ])
            .unwrap();

        let lits = &lits![1, 2, 3][..];

        checker
            .check_step(ProofStep::DeleteClause {
                clause: lits,
                proof: DeleteClauseProof::Satisfied,
            })
            .unwrap();

        checker.add_clause(lits).unwrap();

        checker
            .check_step(ProofStep::DeleteClause {
                clause: lits,
                proof: DeleteClauseProof::Satisfied,
            })
            .unwrap();

        checker
            .check_step(ProofStep::DeleteClause {
                clause: lits,
                proof: DeleteClauseProof::Satisfied,
            })
            .unwrap();

        expect_check_failed(
            checker.check_step(ProofStep::DeleteClause {
                clause: lits,
                proof: DeleteClauseProof::Satisfied,
            }),
            "unknown clause",
        );
    }

    #[test]
    fn clause_not_found() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2, 3;
            ])
            .unwrap();

        expect_check_failed(
            checker.check_step(ProofStep::AtClause {
                redundant: false,
                clause: [][..].into(),
                propagation_hashes: [0][..].into(),
            }),
            "no clause found",
        )
    }

    #[test]
    fn clause_check_failed() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2, 3;
            ])
            .unwrap();

        expect_check_failed(
            checker.check_step(ProofStep::AtClause {
                redundant: false,
                clause: [][..].into(),
                propagation_hashes: [][..].into(),
            }),
            "AT check failed",
        )
    }

    #[test]
    fn delete_clause_not_redundant() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2, 3;
            ])
            .unwrap();

        expect_check_failed(
            checker.check_step(ProofStep::DeleteClause {
                clause: &lits![1, 2, 3],
                proof: DeleteClauseProof::Redundant,
            }),
            "is irredundant",
        )
    }

    #[test]
    fn delete_clause_not_satisfied() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2, 3;
                -2;
                4;
            ])
            .unwrap();

        expect_check_failed(
            checker.check_step(ProofStep::DeleteClause {
                clause: &lits![1, 2, 3],
                proof: DeleteClauseProof::Satisfied,
            }),
            "not satisfied",
        )
    }

    #[test]
    fn delete_clause_not_simplified() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2, 3;
                -3, 4;
            ])
            .unwrap();

        let hashes = [
            checker.clause_hash(&lits![1, 2, 3]),
            checker.clause_hash(&lits![-3, 4]),
        ];

        checker
            .check_step(ProofStep::AtClause {
                redundant: false,
                clause: &lits![1, 2, 4],
                propagation_hashes: &hashes[..],
            })
            .unwrap();

        expect_check_failed(
            checker.check_step(ProofStep::DeleteClause {
                clause: &lits![1, 2, 3],
                proof: DeleteClauseProof::Simplified,
            }),
            "not subsumed",
        )
    }

    #[test]
    fn model_unit_conflict() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1;
                2, 3;
            ])
            .unwrap();

        expect_check_failed(
            checker.check_step(ProofStep::Model(&lits![-1, 2, -3])),
            "conflicts with unit clause",
        )
    }

    #[test]
    fn model_internal_conflict() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                2, 3;
            ])
            .unwrap();

        expect_check_failed(
            checker.check_step(ProofStep::Model(&lits![-1, 1, 2, -3])),
            "conflicting assignment",
        )
    }

    #[test]
    fn model_clause_unsat() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2, 3;
                -1, -2, 3;
                1, -2, -3;
            ])
            .unwrap();

        expect_check_failed(
            checker.check_step(ProofStep::Model(&lits![-1, 2, 3])),
            "does not satisfy clause",
        )
    }

    proptest! {
        #[test]
        fn checked_unsat_via_dimacs(formula in sgen_unsat_formula(1..7usize)) {
            let mut dimacs = vec![];
            let mut proof = vec![];

            let mut solver = Solver::new();

            write_dimacs(&mut dimacs, &formula).unwrap();

            solver.write_proof(&mut proof, ProofFormat::Varisat);

            solver.add_dimacs_cnf(&mut &dimacs[..]).unwrap();

            prop_assert_eq!(solver.solve().ok(), Some(false));

            solver.close_proof().map_err(|e| e.compat())?;

            drop(solver);

            let mut checker = Checker::new();

            checker.add_dimacs_cnf(&mut &dimacs[..]).unwrap();

            checker.check_proof(&mut &proof[..]).unwrap();
        }
    }
}
