//! Internal proof format for the Varisat SAT solver.
use varisat_formula::{Lit, Var};

pub mod binary_format;

mod vli_enc;

// Integer type used to store a hash of a clause.
pub type ClauseHash = u64;

/// Hash a single literal.
///
/// Multiple literals can be combined with xor, as done in [`clause_hash`].
pub fn lit_hash(lit: Lit) -> ClauseHash {
    lit_code_hash(lit.code())
}

/// Hash a single literal from a code.
///
/// This doesn't require the code to correspond a valid literal.
pub fn lit_code_hash(lit_code: usize) -> ClauseHash {
    // Constant based on the golden ratio provides good mixing for the resulting upper bits
    (!(lit_code as u64)).wrapping_mul(0x61c8864680b583ebu64)
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

/// Justifications for a simple clause deletion.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum DeleteClauseProof {
    /// The clause is known to be redundant.
    Redundant,
    /// The clause is irred and subsumed by the clause added in the previous step.
    Simplified,
    /// The clause contains a true literal.
    ///
    /// Also used to justify deletion of tautological clauses.
    Satisfied,
}

/// A single proof step.
///
/// Represents a mutation of the current formula and a justification for the mutation's validity.
#[derive(Copy, Clone, Debug)]
pub enum ProofStep<'a> {
    /// Update the global to solver var mapping.
    ///
    /// For proof checking, the solver variable names are only used for hash computations.
    SolverVarName { global: Var, solver: Option<Var> },
    /// Add a new input clause.
    ///
    /// This is only emitted for clauses added incrementally after an initial solve call.
    AddClause { clause: &'a [Lit] },
    /// Add a clause that is an asymmetric tautoligy (AT).
    ///
    /// Assuming the negation of the clause's literals leads to a unit propagation conflict.
    ///
    /// The second slice contains the hashes of all clauses involved in the resulting conflict. The
    /// order of hashes is the order in which the clauses propagate when all literals of the clause
    /// are set false.
    ///
    /// When generating DRAT proofs the second slice is ignored and may be empty.
    AtClause {
        redundant: bool,
        clause: &'a [Lit],
        propagation_hashes: &'a [ClauseHash],
    },
    /// Unit clauses found by top-level unit-propagation.
    ///
    /// Pairs of unit clauses and the original clause that became unit. Clauses are in chronological
    /// order. This is equivalent to multiple `AtClause` steps where the clause is unit and the
    /// propagation_hashes field contains just one hash, with the difference that this is not output
    /// for DRAT proofs.
    ///
    /// Ignored when generating DRAT proofs.
    UnitClauses(&'a [(Lit, ClauseHash)]),
    /// Delete a clause consisting of the given literals.
    DeleteClause {
        clause: &'a [Lit],
        proof: DeleteClauseProof,
    },
    /// Change the number of clause hash bits used
    ChangeHashBits(u32),
    /// A (partial) assignment that satisfies all clauses and assumptions.
    Model(&'a [Lit]),
    /// Change the active set of assumptions.
    ///
    /// This is checked against future model or failed assumptions steps.
    Assumptions(&'a [Lit]),
    /// A subset of the assumptions that make the formula unsat.
    FailedAssumptions {
        failed_core: &'a [Lit],
        propagation_hashes: &'a [ClauseHash],
    },
    /// Signals the end of a proof.
    ///
    /// A varisat proof must end with this command or else the checker will complain about an
    /// incomplete proof.
    End,
}

impl<'a> ProofStep<'a> {
    /// Does this proof step use clause hashes?
    pub fn contains_hashes(&self) -> bool {
        match self {
            ProofStep::AtClause { .. }
            | ProofStep::UnitClauses(..)
            | ProofStep::FailedAssumptions { .. } => true,

            ProofStep::SolverVarName { .. }
            | ProofStep::AddClause { .. }
            | ProofStep::DeleteClause { .. }
            | ProofStep::ChangeHashBits(..)
            | ProofStep::Model(..)
            | ProofStep::Assumptions(..)
            | ProofStep::End => false,
        }
    }
}
