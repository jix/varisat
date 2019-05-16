//! Proof processor that generates an LRAT proof.
use std::io::{BufWriter, Write};
use std::mem::replace;

use failure::Error;

use crate::lit::Lit;

use super::{CheckedProofStep, ProofProcessor};

/// Proof processor that generates an LRAT proof.
pub struct WriteLrat<'a> {
    binary: bool,
    target: BufWriter<Box<dyn Write + 'a>>,
    delete_open: bool,
    last_added_id: u64,
    buffered_deletes: Vec<u64>,
}

impl<'a> ProofProcessor for WriteLrat<'a> {
    fn process_step(&mut self, step: &CheckedProofStep) -> Result<(), Error> {
        match step {
            &CheckedProofStep::AddClause { .. } => (),
            &CheckedProofStep::DuplicatedClause { .. } => (),
            _ => {
                if !self.buffered_deletes.is_empty() {
                    let buffered_deletes = replace(&mut self.buffered_deletes, vec![]);
                    self.open_delete()?;
                    self.write_ids(&buffered_deletes)?;
                }
            }
        }

        match step {
            &CheckedProofStep::AddClause { id, .. } => {
                self.last_added_id = id;
            }
            &CheckedProofStep::DuplicatedClause { id, .. } => {
                self.last_added_id = id;
                if self.binary {
                    self.open_delete()?;
                    self.write_ids(&[id])?;
                } else {
                    // In the textual format the delete command is prefixed by an id which we do not
                    // know yet.
                    self.buffered_deletes.push(id);
                }
            }
            &CheckedProofStep::AtClause {
                id,
                clause,
                propagations,
                ..
            } => {
                self.close_delete()?;
                self.last_added_id = id;
                self.write_add_step()?;
                self.write_ids(&[id])?;
                self.write_lits(clause)?;
                self.write_sep()?;
                self.write_ids(propagations)?;
                self.write_end()?;
            }
            &CheckedProofStep::DeleteAtClause {
                id,
                keep_as_redundant,
                ..
            } => {
                if !keep_as_redundant {
                    self.open_delete()?;
                    self.write_ids(&[id])?;
                }
            }
            &CheckedProofStep::DeleteClause { id, .. } => {
                self.open_delete()?;
                self.write_ids(&[id])?;
            }
            &CheckedProofStep::MakeIrredundant { .. }
            | &CheckedProofStep::Model { .. }
            | &CheckedProofStep::Assumptions { .. }
            | &CheckedProofStep::FailedAssumptions { .. } => (),
        }
        Ok(())
    }
}

impl<'a> WriteLrat<'a> {
    /// Create a lrat writing processor.
    ///
    /// The proof is written to `target`. If `binary` is false a normal LRAT proof is emitted. If it
    /// is true, the compressed LRAT format is used which is a compact binary encoding. Despite the
    /// name, even a compressed LRAT proof can usually still be compressed a lot using a general
    /// data compression algorithm.
    pub fn new(target: impl Write + 'a, binary: bool) -> WriteLrat<'a> {
        WriteLrat {
            binary,
            target: BufWriter::new(Box::new(target)),
            delete_open: false,
            last_added_id: 0,
            buffered_deletes: vec![],
        }
    }

    /// Write out all steps processed so far.
    ///
    /// This is automatically called when this proof processor is dropped. Calling this explicitly
    /// is recommended to handle possible IO errors.
    pub fn flush(&mut self) -> Result<(), Error> {
        self.close_delete()?;
        self.target.flush()?;
        Ok(())
    }

    /// If necessary begin a batched delete step.
    fn open_delete(&mut self) -> Result<(), Error> {
        if !self.delete_open {
            if !self.binary {
                self.write_ids(&[self.last_added_id])?;
            }
            self.write_delete_step()?;
            self.delete_open = true;
        }
        Ok(())
    }

    /// If necessary end a batched delete step.
    fn close_delete(&mut self) -> Result<(), Error> {
        if self.delete_open {
            self.write_end()?;
            self.delete_open = false;
        }
        Ok(())
    }

    /// Begin a batched delete step.
    fn write_delete_step(&mut self) -> Result<(), Error> {
        if self.binary {
            self.target.write_all(b"d")?;
        } else {
            self.target.write_all(b"d ")?;
        }
        Ok(())
    }

    /// Begin a clause addition step.
    fn write_add_step(&mut self) -> Result<(), Error> {
        if self.binary {
            self.target.write_all(b"a")?;
        }
        Ok(())
    }

    /// Write a list of clause ids.
    fn write_ids(&mut self, ids: &[u64]) -> Result<(), Error> {
        if self.binary {
            for &id in ids {
                leb128::write::unsigned(&mut self.target, (id + 1) * 2)?;
            }
        } else {
            for &id in ids {
                itoa::write(&mut self.target, id + 1)?;
                self.target.write_all(b" ")?;
            }
        }
        Ok(())
    }

    /// Write a list of literals.
    fn write_lits(&mut self, lits: &[Lit]) -> Result<(), Error> {
        if self.binary {
            for &lit in lits {
                leb128::write::unsigned(&mut self.target, lit.code() as u64 + 2)?;
            }
        } else {
            for &lit in lits {
                itoa::write(&mut self.target, lit.to_dimacs())?;
                self.target.write_all(b" ")?;
            }
        }
        Ok(())
    }

    /// End the current step.
    fn write_end(&mut self) -> Result<(), Error> {
        if self.binary {
            self.target.write_all(&[0])?
        } else {
            self.target.write_all(b"0\n")?
        }
        Ok(())
    }

    /// Write a separator.
    fn write_sep(&mut self) -> Result<(), Error> {
        if self.binary {
            self.target.write_all(&[0])?
        } else {
            self.target.write_all(b"0 ")?
        }
        Ok(())
    }
}

impl<'a> Drop for WriteLrat<'a> {
    fn drop(&mut self) {
        let _ignore_errors = self.close_delete();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;

    use std::fs::File;
    use std::path::PathBuf;
    use std::process::{Command, Stdio};

    use tempfile::TempDir;

    use crate::checker::Checker;
    use crate::cnf::CnfFormula;
    use crate::dimacs::write_dimacs;
    use crate::solver::{ProofFormat, Solver};

    use crate::test::sgen_unsat_formula;

    fn check_lrat(tool: &str, cnf_file: &PathBuf, proof_file: &PathBuf) -> Result<bool, Error> {
        let mut child = Command::new(tool)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()?;

        let mut stdin = child.stdin.as_mut().unwrap();
        writeln!(&mut stdin, "(lrat-check {:?} {:?})", cnf_file, proof_file)?;

        let output = child.wait_with_output()?;
        let stdout = std::str::from_utf8(&output.stdout)?;

        Ok(stdout.contains("s VERIFIED"))
    }

    fn solve_and_check_lrat(
        formula: CnfFormula,
        binary: bool,
        direct: bool,
    ) -> Result<bool, Error> {
        let tmp = TempDir::new()?;

        let lrat_proof = tmp.path().join("proof.lrat");
        let cnf_file = tmp.path().join("input.cnf");

        let mut dimacs = vec![];
        let mut proof = vec![];

        let mut write_lrat = WriteLrat::new(File::create(&lrat_proof)?, binary);
        write_dimacs(&mut File::create(&cnf_file)?, &formula)?;

        let mut solver = Solver::new();

        write_dimacs(&mut dimacs, &formula).unwrap();

        if direct {
            solver.add_proof_processor(&mut write_lrat);
        } else {
            solver.write_proof(&mut proof, ProofFormat::Varisat);
        }

        solver.add_dimacs_cnf(&mut &dimacs[..]).unwrap();

        assert_eq!(solver.solve().ok(), Some(false));

        solver.close_proof()?;

        drop(solver);

        if !direct {
            let mut checker = Checker::new();
            checker.add_processor(&mut write_lrat);

            checker.add_dimacs_cnf(&mut &dimacs[..]).unwrap();

            checker.check_proof(&mut &proof[..]).unwrap();
        }

        drop(write_lrat);

        check_lrat(
            if binary { "check-clrat" } else { "check-lrat" },
            &cnf_file,
            &lrat_proof,
        )
    }

    #[cfg_attr(not(test_check_lrat), ignore)]
    #[test]
    fn duplicated_clause_lrat() {
        for &binary in [false, true].iter() {
            for &direct in [false, true].iter() {
                assert!(
                    solve_and_check_lrat(
                        cnf_formula![
                            1, 2;
                            1, 2;
                            -1, -2;
                            3;
                            -3, -1, 2;
                            -4, 1, -2;
                            4;
                        ],
                        binary,
                        direct
                    )
                    .unwrap(),
                    "binary: {:?} direct: {:?}",
                    binary,
                    direct
                );
            }
        }
    }

    #[cfg_attr(not(test_check_lrat), ignore)]
    #[test]
    fn unit_conflict_lrat() {
        for &binary in [false, true].iter() {
            for &direct in [false, true].iter() {
                assert!(
                    solve_and_check_lrat(
                        cnf_formula![
                            1;
                            2, 3;
                            -1;
                            4, 5;
                        ],
                        binary,
                        direct
                    )
                    .unwrap(),
                    "binary: {:?} direct: {:?}",
                    binary,
                    direct
                );
            }
        }
    }

    proptest! {

        #[cfg_attr(not(test_check_lrat), ignore)]
        #[test]
        fn sgen_unsat_lrat(
            formula in sgen_unsat_formula(1..7usize),
            binary in proptest::bool::ANY,
            direct in proptest::bool::ANY,
        ) {
            prop_assert!(solve_and_check_lrat(formula, binary, direct).unwrap());
        }
    }
}
