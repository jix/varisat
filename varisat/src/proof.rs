//! Proof generation.

use std::borrow::Cow;
use std::io::{sink, BufWriter, Write};

use serde::{Deserialize, Serialize};

use crate::lit::Lit;

/// Proof formats that can be generated during solving.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum ProofFormat {
    Varisat,
    Drat,
    BinaryDrat,
}

/// Integer type used to store a hash of a clause.
pub type ClauseHash = u64;

/// Hash a single literal.
///
/// Multiple literals can be combined with xor, as done in [`clause_hash`].
pub fn lit_hash(lit: Lit) -> ClauseHash {
    // Constant based on the golden ratio provides good mixing for the resulting upper bits
    (!(lit.code() as u64)).wrapping_mul(0x61c8864680b583ebu64)
}

/// A fast hash function for clauses (or other *sets* of literals).
///
/// This hash function interprets the given slice as a set and will not change when the input is
/// permuted. It does not handle duplicated items.
pub fn clause_hash(lits: &[Lit]) -> ClauseHash {
    let mut hash = 0;
    for &lit in lits {
        hash ^= lit_hash(lit);
    }
    hash
}

/// A single proof step.
///
/// Represents a mutation of the current formula and a justification for the mutation's validity.
#[derive(Serialize, Deserialize, Debug)]
pub enum ProofStep<'a> {
    /// Add a clause justified by reverse unit propagation.
    ///
    /// The second slice contains the hashes of all clauses involved in the resulting conflict. The
    /// order of hashes is the order in which the clauses propagate when all literals of the clause
    /// are set false.
    ///
    /// When generating DRAT proofs the second slice is ignored and may be empty.
    RupClause(Cow<'a, [Lit]>, Cow<'a, [ClauseHash]>),
    /// Unit clauses found by top-level unit-propagation.
    ///
    /// The first slice is a list of units found. The second is a list of hashes of the respective
    /// clauses that became unit.
    ///
    /// Ignored when generating DRAT proofs.
    UnitClauses(Cow<'a, [(Lit, ClauseHash)]>),
    /// Delete a clause consisting of the given literals.
    DeleteClause(Cow<'a, [Lit]>),
}

/// Proof generation.
pub struct Proof {
    format: Option<ProofFormat>,
    target: BufWriter<Box<dyn Write>>,
}

impl Default for Proof {
    fn default() -> Proof {
        Proof {
            format: None,
            target: BufWriter::new(Box::new(sink())),
        }
    }
}

macro_rules! handle_io_errors {
    ($s:expr, $e:expr) => {{
        let res = $e;
        $s.handle_io_errors(res)
    }};
}

impl Proof {
    /// Start writing proof steps to the given target with the given format.
    pub fn write_proof(&mut self, target: impl Write + 'static, format: ProofFormat) {
        self.format = Some(format);
        self.target = BufWriter::new(Box::new(target))
    }

    /// Stop writing proof steps.
    pub fn close_proof(&mut self) {
        // We need to explicitly flush to handle IO errors.
        handle_io_errors!(self, self.target.flush());
        self.format = None;
        self.target = BufWriter::new(Box::new(sink()));
    }

    /// Whether proof generation is active.
    pub fn is_active(&self) -> bool {
        self.format.is_some()
    }

    /// Whether clause hashes are required for steps that support them.
    pub fn clause_hashes_required(&self) -> bool {
        match self.format {
            Some(ProofFormat::Varisat) => true,
            Some(ProofFormat::Drat) | Some(ProofFormat::BinaryDrat) => false,
            None => false,
        }
    }

    /// Whether unit clauses discovered through unit propagation have to be proven.
    pub fn prove_propagated_unit_clauses(&self) -> bool {
        match self.format {
            Some(ProofFormat::Varisat) => true,
            Some(ProofFormat::Drat) | Some(ProofFormat::BinaryDrat) => false,
            None => false,
        }
    }

    /// Add a step to the proof.
    ///
    /// Ignored when proof generation is disabled.
    pub fn add_step<'a>(&'a mut self, step: &'a ProofStep<'a>) {
        match self.format {
            None => (),
            Some(ProofFormat::Varisat) => self.write_varisat_step(step),
            Some(ProofFormat::Drat) | Some(ProofFormat::BinaryDrat) => self.write_drat_step(step),
        }
    }

    /// Writes a proof step in our own format.
    fn write_varisat_step<'a>(&'a mut self, step: &'a ProofStep<'a>) {
        handle_io_errors!(self, bincode::serialize_into(&mut self.target, step));
    }

    /// Writes a proof step in DRAT or binary DRAT format.
    fn write_drat_step<'a>(&'a mut self, step: &'a ProofStep<'a>) {
        match step {
            ProofStep::RupClause(clause, ..) => {
                self.drat_add_clause();
                self.drat_literals(&clause)
            }
            ProofStep::DeleteClause(clause) => {
                self.drat_delete_clause();
                self.drat_literals(&clause[..]);
            }
            ProofStep::UnitClauses(..) => (),
        }
    }

    /// Writes an add clause step to the DRAT proof.
    fn drat_add_clause(&mut self) {
        if self.format == Some(ProofFormat::BinaryDrat) {
            handle_io_errors!(self, self.target.write_all(b"a"));
        }
    }

    /// Writes a delete clause step to the DRAT proof.
    fn drat_delete_clause(&mut self) {
        if self.format == Some(ProofFormat::BinaryDrat) {
            handle_io_errors!(self, self.target.write_all(b"d"));
        } else {
            handle_io_errors!(self, self.target.write_all(b"d "));
        }
    }

    /// Writes the literals of a clause for a step in a DRAT proof.
    fn drat_literals(&mut self, literals: &[Lit]) {
        if self.format == Some(ProofFormat::BinaryDrat) {
            for &lit in literals {
                let drat_code = lit.code() as u64 + 2;
                handle_io_errors!(self, leb128::write::unsigned(&mut self.target, drat_code));
            }
            handle_io_errors!(self, self.target.write_all(&[0]));
        } else {
            for &lit in literals {
                handle_io_errors!(self, itoa::write(&mut self.target, lit.to_dimacs()));
                handle_io_errors!(self, self.target.write_all(b" "));
            }
            handle_io_errors!(self, self.target.write_all(b"0\n"));
        }
    }

    /// Handles IO errors.
    ///
    /// Right now this panics. In the future it should set an error flag that will be checked in the
    /// solver main loop to abort when proof writing failed.
    fn handle_io_errors<V, E: std::fmt::Debug>(&self, result: Result<V, E>) -> Option<V> {
        // TODO better error handling
        // on error we want to abort solving eventually but not panic
        // we also don't want to force error handling on proof generating code
        Some(result.expect("unable to write to proof file"))
    }
}
