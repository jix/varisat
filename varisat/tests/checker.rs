//! Checker tests, that require a Solver instance, so they cannot be unit tests of the
//! varisat-checker crate.

use failure::{Error, Fail};

use proptest::prelude::*;

use varisat::checker::{Checker, ProofTranscriptProcessor, ProofTranscriptStep};
use varisat::{dimacs::write_dimacs, CnfFormula, ExtendFormula, Lit, ProofFormat, Solver, Var};
use varisat_formula::test::{conditional_pigeon_hole, sgen_unsat_formula};

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

    #[test]
    fn sgen_checked_unsat_incremental_clauses(formula in sgen_unsat_formula(1..7usize)) {
        let mut proof = vec![];

        let mut solver = Solver::new();
        solver.write_proof(&mut proof, ProofFormat::Varisat);

        let mut expected_models = 0;

        // Add all clauses incrementally so they are recorded in the proof
        solver.solve().unwrap();
        expected_models += 1;

        let mut last_state = Some(true);

        for clause in formula.iter() {
            solver.add_clause(clause);

            let state = solver.solve().ok();
            if state != last_state {
                prop_assert_eq!(state, Some(false));
                prop_assert_eq!(last_state, Some(true));
                last_state = state;
            }
            if state == Some(true) {
                expected_models += 1;
            }
        }

        prop_assert_eq!(last_state, Some(false));

        drop(solver);

        #[derive(Default)]
        struct FoundModels {
            counter: usize,
            unsat: bool,
        }

        impl ProofTranscriptProcessor for FoundModels {
            fn process_step(
                &mut self,
                step: &ProofTranscriptStep,
            ) -> Result<(), Error> {
                if let ProofTranscriptStep::Model { .. } = step {
                    self.counter += 1;
                } else if let ProofTranscriptStep::Unsat = step {
                    self.unsat = true;
                }
                Ok(())
            }
        }

        let mut found_models = FoundModels::default();
        let mut checker = Checker::new();
        checker.add_transcript(&mut found_models);
        checker.check_proof(&mut &proof[..]).unwrap();

        prop_assert_eq!(found_models.counter, expected_models);
        prop_assert!(found_models.unsat);
    }

    #[test]
    fn pigeon_hole_checked_unsat_assumption_core(
        (enable_row, columns, formula) in conditional_pigeon_hole(1..5usize, 1..5usize),
    ) {
        let mut proof = vec![];

        let mut solver = Solver::new();
        solver.write_proof(&mut proof, ProofFormat::Varisat);

        let mut expected_sat = 0;
        let mut expected_unsat = 0;

        solver.solve().unwrap();
        expected_sat += 1;
        solver.add_formula(&formula);

        prop_assert_eq!(solver.solve().ok(), Some(true));
        expected_sat += 1;

        let mut assumptions = enable_row;

        assumptions.push(Lit::positive(Var::from_index(formula.var_count() + 10)));

        solver.assume(&assumptions);

        prop_assert_eq!(solver.solve().ok(), Some(false));
        expected_unsat += 1;

        let mut candidates = solver.failed_core().unwrap().to_owned();
        let mut core: Vec<Lit> = vec![];

        while !candidates.is_empty() {

            solver.assume(&candidates[0..candidates.len() - 1]);

            match solver.solve() {
                Err(_) => unreachable!(),
                Ok(true) => {
                    expected_sat += 1;
                    let skipped = *candidates.last().unwrap();
                    core.push(skipped);

                    let single_clause = CnfFormula::from(Some([skipped]));
                    solver.add_formula(&single_clause);
                },
                Ok(false) => {
                    expected_unsat += 1;
                    candidates = solver.failed_core().unwrap().to_owned();
                }
            }
        }

        prop_assert_eq!(core.len(), columns + 1);

        drop(solver);

        #[derive(Default)]
        struct CountResults {
            sat: usize,
            unsat: usize,
        }

        impl ProofTranscriptProcessor for CountResults {
            fn process_step(
                &mut self,
                step: &ProofTranscriptStep,
            ) -> Result<(), Error> {
                match step {
                    ProofTranscriptStep::Model { .. } => {
                        self.sat += 1;
                    }
                    ProofTranscriptStep::Unsat
                    | ProofTranscriptStep::FailedAssumptions { .. } => {
                        self.unsat += 1;
                    }
                    _ => (),
                }
                Ok(())
            }
        }

        let mut count_results = CountResults::default();
        let mut checker = Checker::new();
        checker.add_transcript(&mut count_results);
        checker.check_proof(&mut &proof[..]).unwrap();

        prop_assert_eq!(count_results.sat, expected_sat);
        prop_assert_eq!(count_results.unsat, expected_unsat);
    }
}
