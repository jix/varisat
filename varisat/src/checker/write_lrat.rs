//! Proof processor that generates an LRAT proof.
use std::io::{BufWriter, Write};
use std::mem::replace;

use failure::{bail, Error};

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
            &CheckedProofStep::DeleteClause { id, .. } => {
                self.open_delete()?;

                self.write_ids(&[id])?;
            }
            _ => bail!("LRAT doesn't support proof step {:?}", step),
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
