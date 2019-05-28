use varisat::checker::{ProofTranscriptProcessor, ProofTranscriptStep};

use failure::Error;

/// Steps that will be summarized
#[derive(Copy, Clone, Eq, PartialEq)]
enum SummaryStep {
    WitnessVar,
    SampleVar,
    HideVar,
    ObserveInternalVar,
    AddClause,
}

/// Prints a simple transcript of the proof.
///
/// This shows whether the formula was proven unsatisfiable or whether a model is found.
#[derive(Default)]
pub struct Transcript {
    last_step: Option<SummaryStep>,
    counter: usize,
}

impl Transcript {
    /// Print a summary of steps that appear repeatedly.
    fn print_summary(&mut self, step: Option<SummaryStep>) {
        if self.last_step == step {
            self.counter += 1;
        } else {
            match self.last_step {
                None => (),
                Some(SummaryStep::WitnessVar) => {
                    println!("t WITNESS {} VARIABLES ", self.counter);
                }
                Some(SummaryStep::SampleVar) => {
                    println!("t SAMPLE {} VARIABLES ", self.counter);
                }
                Some(SummaryStep::HideVar) => {
                    println!("t HIDE {} VARIABLES ", self.counter);
                }
                Some(SummaryStep::ObserveInternalVar) => {
                    println!("t OBSERVE {} INTERNAL VARIABLES ", self.counter);
                }
                Some(SummaryStep::AddClause) => {
                    println!("t ADD {} CLAUSES ", self.counter);
                }
            }

            self.counter = 1;
            self.last_step = step;
        }
    }
}

impl ProofTranscriptProcessor for Transcript {
    fn process_step(&mut self, step: &ProofTranscriptStep) -> Result<(), Error> {
        match &step {
            ProofTranscriptStep::WitnessVar { .. } => {
                self.print_summary(Some(SummaryStep::WitnessVar));
            }
            ProofTranscriptStep::SampleVar { .. } => {
                self.print_summary(Some(SummaryStep::SampleVar));
            }
            ProofTranscriptStep::HideVar { .. } => {
                self.print_summary(Some(SummaryStep::HideVar));
            }
            ProofTranscriptStep::ObserveInternalVar { .. } => {
                self.print_summary(Some(SummaryStep::ObserveInternalVar));
            }
            ProofTranscriptStep::AddClause { .. } => {
                self.print_summary(Some(SummaryStep::AddClause));
            }
            ProofTranscriptStep::Unsat => {
                self.print_summary(None);
                println!("t UNSAT");
            }
            ProofTranscriptStep::Model { .. } => {
                self.print_summary(None);
                println!("t SAT");
            }
            ProofTranscriptStep::Assume { assumptions } => {
                self.print_summary(None);
                println!("t ASSUME {} LITERALS", assumptions.len());
            }
            ProofTranscriptStep::FailedAssumptions { failed_core, .. } => {
                self.print_summary(None);
                println!("t UNSAT WITH {} ASSUMPTIONS", failed_core.len());
            }
        }
        Ok(())
    }
}
