use partial_ref::{partial, PartialRef};

use failure::Error;
use varisat_formula::{Lit, Var};

use crate::context::{parts::*, Context};
use crate::transcript::{self, ProofTranscriptProcessor};
use crate::variables::SamplingMode;
use crate::CheckerError;

/// A single step of a proof.
///
/// Clauses are identified by a unique increasing id assigned by the checker. Whenever the literals
/// of a clause are included in a step, they are sorted and free of duplicates.
#[derive(Debug)]
pub enum CheckedProofStep<'a> {
    /// Updates the corresponding user variable for a proof variable.
    UserVar {
        var: Var,
        user_var: Option<CheckedUserVar>,
    },
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
    /// A tautological clause of the input formula.
    ///
    /// Tautological clauses can be completely ignored. This step is only used to give an id to a
    /// tautological input clause.
    TautologicalClause { id: u64, clause: &'a [Lit] },
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
    /// Deletion of a resolution asymmetric tautology w.r.t the remaining irredundant caluses.
    ///
    /// The pivot is always a hidden variable.
    DeleteRatClause {
        id: u64,
        keep_as_redundant: bool,
        clause: &'a [Lit],
        pivot: Lit,
        propagations: &'a ResolutionPropagations,
    },
    /// Make a redundant clause irredundant.
    MakeIrredundant { id: u64, clause: &'a [Lit] },
    /// A (partial) assignment that satisfies all clauses and assumptions.
    Model { assignment: &'a [Lit] },
    /// Change the active set of assumptions.
    Assumptions { assumptions: &'a [Lit] },
    /// Subset of assumptions incompatible with the formula.
    ///
    /// The proof consists of showing that the negation of the assumptions is an AT wrt. the
    /// formula.
    FailedAssumptions {
        failed_core: &'a [Lit],
        propagations: &'a [u64],
    },
}

/// Sampling mode of a user variable.
#[derive(Debug)]
pub enum CheckedSamplingMode {
    Sample,
    Witness,
}

/// Corresponding user variable for a proof variable.
#[derive(Debug)]
pub struct CheckedUserVar {
    pub user_var: Var,
    pub sampling_mode: CheckedSamplingMode,
    pub new_var: bool,
}

/// A list of clauses to resolve and propagations to show that the resolvent is an AT.
#[derive(Debug)]
pub struct ResolutionPropagations {
    // TODO implement ResolutionPropagations
}

/// Checker data available to proof processors.
#[derive(Copy, Clone)]
pub struct CheckerData<'a, 'b>(pub partial!('a Context<'b>, VariablesP));

impl<'a, 'b> CheckerData<'a, 'b> {
    /// User variable corresponding to proof variable.
    ///
    /// Returns `None` if the proof variable is an internal or hidden variable.
    pub fn user_from_proof_var(self, proof_var: Var) -> Option<Var> {
        let variables = self.0.part(VariablesP);
        variables
            .var_data
            .get(proof_var.index())
            .and_then(|var_data| {
                var_data.user_var.or_else(|| {
                    // This is needed as yet another workaround to enable independently loading the
                    // initial formula and proof.
                    // TODO can this be solved in a better way?
                    if var_data.sampling_mode == SamplingMode::Sample {
                        Some(proof_var)
                    } else {
                        None
                    }
                })
            })
    }
}

/// Implement to process proof steps.
pub trait ProofProcessor {
    fn process_step(&mut self, step: &CheckedProofStep, data: CheckerData) -> Result<(), Error>;
}

/// Registry of proof and transcript processors.
#[derive(Default)]
pub struct Processing<'a> {
    /// Registered proof processors.
    pub processors: Vec<&'a mut dyn ProofProcessor>,
    /// Registered transcript processors.
    pub transcript_processors: Vec<&'a mut dyn ProofTranscriptProcessor>,
    /// Proof step to transcript step conversion.
    transcript: transcript::Transcript,
}

impl<'a> Processing<'a> {
    /// Process a single step
    pub fn step<'b>(
        &mut self,
        step: &CheckedProofStep<'b>,
        data: CheckerData,
    ) -> Result<(), CheckerError> {
        for processor in self.processors.iter_mut() {
            if let Err(err) = processor.process_step(step, data) {
                return Err(CheckerError::ProofProcessorError { cause: err });
            }
        }
        if !self.transcript_processors.is_empty() {
            if let Some(transcript_step) = self.transcript.transcript_step(step, data) {
                for processor in self.transcript_processors.iter_mut() {
                    if let Err(err) = processor.process_step(&transcript_step) {
                        return Err(CheckerError::ProofProcessorError { cause: err });
                    }
                }
            }
        }

        Ok(())
    }
}

/// Process a single step
pub fn process_step<'a, 'b>(
    mut ctx: partial!(Context<'a>, mut ProcessingP<'a>, VariablesP),
    step: &CheckedProofStep<'b>,
) -> Result<(), CheckerError> {
    let (processing, mut ctx) = ctx.split_part_mut(ProcessingP);
    processing.step(step, CheckerData(ctx.borrow()))
}
