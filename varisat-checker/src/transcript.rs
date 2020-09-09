//! Proof transcripts.
use anyhow::Error;

use varisat_formula::{Lit, Var};

use crate::processing::{CheckedProofStep, CheckedSamplingMode, CheckedUserVar, CheckerData};

/// Step of a proof transcript.
///
/// The proof transcript contains the solver queries and results that correspond to a checked proof.
///
/// The transcript uses the same variable numbering as used for solver calls.
#[derive(Debug)]
pub enum ProofTranscriptStep<'a> {
    WitnessVar { var: Var },
    SampleVar { var: Var },
    HideVar { var: Var },
    ObserveInternalVar { var: Var },
    AddClause { clause: &'a [Lit] },
    Unsat,
    Model { assignment: &'a [Lit] },
    Assume { assumptions: &'a [Lit] },
    FailedAssumptions { failed_core: &'a [Lit] },
}

/// Implement to process transcript steps.
pub trait ProofTranscriptProcessor {
    /// Process a single proof transcript step.
    fn process_step(&mut self, step: &ProofTranscriptStep) -> Result<(), Error>;
}

/// Create a transcript from proof steps
#[derive(Default)]
pub(crate) struct Transcript {
    lit_buf: Vec<Lit>,
}

impl Transcript {
    /// If a checked proof step has a corresponding transcript step, return that.
    pub fn transcript_step(
        &mut self,
        step: &CheckedProofStep,
        data: CheckerData,
    ) -> Option<ProofTranscriptStep> {
        match step {
            CheckedProofStep::UserVar { var, user_var } => match user_var {
                None => Some(ProofTranscriptStep::HideVar {
                    var: data.user_from_proof_var(*var).unwrap(),
                }),

                Some(CheckedUserVar {
                    sampling_mode: CheckedSamplingMode::Sample,
                    new_var: true,
                    ..
                }) => None,

                Some(CheckedUserVar {
                    user_var,
                    sampling_mode: CheckedSamplingMode::Witness,
                    new_var: true,
                }) => Some(ProofTranscriptStep::ObserveInternalVar { var: *user_var }),

                Some(CheckedUserVar {
                    user_var,
                    sampling_mode: CheckedSamplingMode::Witness,
                    new_var: false,
                }) => Some(ProofTranscriptStep::WitnessVar { var: *user_var }),

                Some(CheckedUserVar {
                    user_var,
                    sampling_mode: CheckedSamplingMode::Sample,
                    new_var: false,
                }) => Some(ProofTranscriptStep::SampleVar { var: *user_var }),
            },
            CheckedProofStep::AddClause { clause, .. }
            | CheckedProofStep::DuplicatedClause { clause, .. }
            | CheckedProofStep::TautologicalClause { clause, .. } => {
                self.lit_buf.clear();
                self.lit_buf.extend(clause.iter().map(|&lit| {
                    lit.map_var(|var| {
                        data.user_from_proof_var(var)
                            .expect("hidden variable in clause")
                    })
                }));
                Some(ProofTranscriptStep::AddClause {
                    clause: &self.lit_buf,
                })
            }
            CheckedProofStep::AtClause { clause, .. } => {
                if clause.is_empty() {
                    Some(ProofTranscriptStep::Unsat)
                } else {
                    None
                }
            }
            CheckedProofStep::Model { assignment } => {
                self.lit_buf.clear();
                self.lit_buf.extend(assignment.iter().flat_map(|&lit| {
                    data.user_from_proof_var(lit.var())
                        .map(|var| var.lit(lit.is_positive()))
                }));
                Some(ProofTranscriptStep::Model {
                    assignment: &self.lit_buf,
                })
            }
            CheckedProofStep::Assumptions { assumptions } => {
                self.lit_buf.clear();
                self.lit_buf.extend(assumptions.iter().map(|&lit| {
                    lit.map_var(|var| {
                        data.user_from_proof_var(var)
                            .expect("hidden variable in assumptions")
                    })
                }));
                Some(ProofTranscriptStep::Assume {
                    assumptions: &self.lit_buf,
                })
            }
            CheckedProofStep::FailedAssumptions { failed_core, .. } => {
                self.lit_buf.clear();
                self.lit_buf.extend(failed_core.iter().map(|&lit| {
                    lit.map_var(|var| {
                        data.user_from_proof_var(var)
                            .expect("hidden variable in assumptions")
                    })
                }));
                Some(ProofTranscriptStep::FailedAssumptions {
                    failed_core: &self.lit_buf,
                })
            }
            _ => None,
        }
    }
}
