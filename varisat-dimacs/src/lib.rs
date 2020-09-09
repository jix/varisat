//! DIMCAS CNF parser and writer for the Varisat SAT solver.

use std::{borrow::Borrow, io, mem::replace};

use varisat_formula::{CnfFormula, ExtendFormula, Lit, Var};

use anyhow::Error;
use thiserror::Error;

/// Possible errors while parsing a DIMACS CNF formula.
#[derive(Debug, Error)]
pub enum ParserError {
    #[error(
        "line {}: Unexpected character in DIMACS CNF input: '{}'",
        line,
        unexpected
    )]
    UnexpectedInput { line: usize, unexpected: char },
    #[error(
        "line {}: Literal index is too large: {}{}...",
        line,
        index,
        final_digit
    )]
    LiteralTooLarge {
        line: usize,
        index: usize,
        final_digit: usize,
    },
    #[error("line {}: Invalid header syntax: {}", line, header)]
    InvalidHeader { line: usize, header: String },
    #[error("line {}: Unterminated clause", line)]
    UnterminatedClause { line: usize },
    #[error(
        "Formula has {} variables while the header specifies {} variables",
        var_count,
        header_var_count
    )]
    VarCount {
        var_count: usize,
        header_var_count: usize,
    },
    #[error(
        "Formula has {} clauses while the header specifies {} clauses",
        clause_count,
        header_clause_count
    )]
    ClauseCount {
        clause_count: usize,
        header_clause_count: usize,
    },
    #[error("Parser invoked after a previous error")]
    PreviousError,
}

/// Variable and clause count present in a DIMACS CNF header.
#[derive(Copy, Clone, Debug)]
pub struct DimacsHeader {
    pub var_count: usize,
    pub clause_count: usize,
}

/// Parser for DIMACS CNF files.
///
/// This parser can consume the input in chunks while also producing the parsed result in chunks.
#[derive(Default)]
pub struct DimacsParser {
    formula: CnfFormula,
    partial_clause: Vec<Lit>,
    header: Option<DimacsHeader>,

    line_number: usize,
    clause_count: usize,
    partial_lit: usize,
    negate_next_lit: bool,

    in_lit: bool,
    in_comment_or_header: bool,
    in_header: bool,
    start_of_line: bool,
    error: bool,

    header_line: Vec<u8>,
}

impl DimacsParser {
    /// Create a new DIMACS CNF parser.
    pub fn new() -> DimacsParser {
        DimacsParser {
            formula: CnfFormula::new(),
            partial_clause: vec![],
            header: None,

            line_number: 1,
            clause_count: 0,
            partial_lit: 0,
            negate_next_lit: false,

            in_lit: false,
            in_comment_or_header: false,
            in_header: false,
            start_of_line: true,
            error: false,

            header_line: vec![],
        }
    }

    /// Parse the given input and check the header if present.
    ///
    /// This parses the whole input into a single [`CnfFormula`](varisat_formula::CnfFormula).
    /// Incremental parsing is possible using [`parse_incremental`](DimacsParser::parse_incremental)
    /// or the [`parse_chunk`](DimacsParser::parse_chunk) method.
    pub fn parse(input: impl io::Read) -> Result<CnfFormula, Error> {
        Ok(Self::parse_incremental(input, |_| Ok(()))?.take_formula())
    }

    /// Parse the given input incrementally and check the header if present.
    ///
    /// The callback is invoked repeatedly with a reference to the parser. The callback can process
    /// the formula incrementally by calling [`take_formula`](DimacsParser::take_formula) on the
    /// passed argument.
    pub fn parse_incremental(
        input: impl io::Read,
        mut callback: impl FnMut(&mut DimacsParser) -> Result<(), Error>,
    ) -> Result<DimacsParser, Error> {
        use io::BufRead;

        let mut buffer = io::BufReader::new(input);
        let mut parser = Self::new();

        loop {
            let data = buffer.fill_buf()?;
            if data.is_empty() {
                break;
            }
            parser.parse_chunk(data)?;
            let len = data.len();
            buffer.consume(len);

            callback(&mut parser)?;
        }
        parser.eof()?;
        callback(&mut parser)?;
        parser.check_header()?;

        Ok(parser)
    }

    /// Parse a chunk of input.
    ///
    /// After parsing the last chunk call the [`eof`](DimacsParser::eof) method.
    ///
    /// If this method returns an error, the parser is in an invalid state and cannot parse further
    /// chunks.
    pub fn parse_chunk(&mut self, chunk: &[u8]) -> Result<(), ParserError> {
        if self.error {
            return Err(ParserError::PreviousError);
        }
        for &byte in chunk.iter() {
            if byte == b'\n' {
                self.line_number += 1;
            }
            match byte {
                b'\n' | b'\r' if self.in_comment_or_header => {
                    if self.in_header {
                        self.in_header = false;
                        self.parse_header_line()?;
                    }
                    self.in_comment_or_header = false;
                    self.start_of_line = true
                }
                _ if self.in_comment_or_header => {
                    if self.in_header {
                        self.header_line.push(byte);
                    }
                }
                b'0'..=b'9' => {
                    self.in_lit = true;
                    let digit = (byte - b'0') as usize;

                    const CAN_OVERFLOW: usize = Var::max_count() / 10;
                    const OVERFLOW_DIGIT: usize = Var::max_count() % 10;

                    // Overflow check that is fast but still works if LitIdx has the same size as
                    // usize
                    if CAN_OVERFLOW <= self.partial_lit {
                        let carry = (digit <= OVERFLOW_DIGIT) as usize;

                        if CAN_OVERFLOW + carry <= self.partial_lit {
                            self.error = true;
                            return Err(ParserError::LiteralTooLarge {
                                line: self.line_number,
                                index: self.partial_lit,
                                final_digit: digit,
                            });
                        }
                    }

                    self.partial_lit = self.partial_lit * 10 + digit;

                    self.start_of_line = false
                }
                b'-' if !self.negate_next_lit && !self.in_lit => {
                    self.negate_next_lit = true;
                    self.start_of_line = false
                }
                b' ' | b'\n' | b'\r' if !self.negate_next_lit || self.in_lit => {
                    self.finish_literal();
                    self.negate_next_lit = false;
                    self.in_lit = false;
                    self.partial_lit = 0;
                    self.start_of_line = byte != b' ';
                }
                b'c' if self.start_of_line => {
                    self.in_comment_or_header = true;
                }
                b'p' if self.start_of_line && self.header.is_none() => {
                    self.in_comment_or_header = true;
                    self.in_header = true;
                    self.header_line.push(b'p');
                }
                _ => {
                    self.error = true;
                    return Err(ParserError::UnexpectedInput {
                        line: self.line_number,
                        unexpected: byte as char,
                    });
                }
            }
        }

        Ok(())
    }

    /// Finish parsing the input.
    ///
    /// This does not check whether the header information was correct, call
    /// [`check_header`](DimacsParser::check_header) for this.
    pub fn eof(&mut self) -> Result<(), ParserError> {
        if self.in_header {
            self.parse_header_line()?;
        }

        self.finish_literal();

        if !self.partial_clause.is_empty() {
            return Err(ParserError::UnterminatedClause {
                line: self.line_number,
            });
        }

        Ok(())
    }

    /// Verifies the header information when present.
    ///
    /// Does nothing when the input doesn't contain a header.
    pub fn check_header(&self) -> Result<(), ParserError> {
        if let Some(header) = self.header {
            let var_count = self.formula.var_count();
            if var_count != header.var_count {
                return Err(ParserError::VarCount {
                    var_count,
                    header_var_count: header.var_count,
                });
            }

            if self.clause_count != header.clause_count {
                return Err(ParserError::ClauseCount {
                    clause_count: self.clause_count,
                    header_clause_count: header.clause_count,
                });
            }
        }

        Ok(())
    }

    /// Returns the subformula of everything parsed since the last call to this method.
    ///
    /// To parse the whole input into a single [`CnfFormula`](varisat_formula::CnfFormula), simply
    /// call this method once after calling [`eof`](DimacsParser::eof). For incremental parsing this
    /// method can be invoked after each call of [`parse_chunk`](DimacsParser::parse_chunk).
    ///
    /// The variable count of the returned formula will be the maximum of the variable count so far
    /// and the variable count of the header if present.
    pub fn take_formula(&mut self) -> CnfFormula {
        let mut new_formula = CnfFormula::new();
        new_formula.set_var_count(self.formula.var_count());
        replace(&mut self.formula, new_formula)
    }

    /// Return the DIMACS CNF header data if present.
    pub fn header(&self) -> Option<DimacsHeader> {
        self.header
    }

    /// Number of clauses parsed.
    pub fn clause_count(&self) -> usize {
        self.clause_count
    }

    /// Number of variables in the parsed formula.
    pub fn var_count(&self) -> usize {
        self.formula.var_count()
    }

    fn finish_literal(&mut self) {
        if self.in_lit {
            if self.partial_lit == 0 {
                self.formula.add_clause(&self.partial_clause);
                self.partial_clause.clear();
                self.clause_count += 1;
            } else {
                self.partial_clause
                    .push(Var::from_dimacs(self.partial_lit as isize).lit(!self.negate_next_lit));
            }
        }
    }

    fn parse_header_line(&mut self) -> Result<(), ParserError> {
        let header_line = String::from_utf8_lossy(&self.header_line).into_owned();

        if !header_line.starts_with("p ") {
            return self.invalid_header(header_line);
        }

        let mut header_values = header_line[2..].split_whitespace();

        if header_values.next() != Some("cnf") {
            return self.invalid_header(header_line);
        }

        let var_count: usize = match header_values
            .next()
            .and_then(|value| str::parse(value).ok())
        {
            None => return self.invalid_header(header_line),
            Some(value) => value,
        };

        if var_count > Var::max_count() {
            self.error = true;
            return Err(ParserError::LiteralTooLarge {
                line: self.line_number,
                index: var_count / 10,
                final_digit: var_count % 10,
            });
        }

        let clause_count: usize = match header_values
            .next()
            .and_then(|value| str::parse(value).ok())
        {
            None => return self.invalid_header(header_line),
            Some(value) => value,
        };

        if header_values.next().is_some() {
            return self.invalid_header(header_line);
        }

        self.header = Some(DimacsHeader {
            var_count,
            clause_count,
        });

        self.formula.set_var_count(var_count);

        Ok(())
    }

    fn invalid_header(&mut self, header_line: String) -> Result<(), ParserError> {
        self.error = true;
        Err(ParserError::InvalidHeader {
            line: self.line_number,
            header: header_line,
        })
    }
}

/// Write a DIMACS CNF header.
///
/// Can be used with [`write_dimacs_clauses`] to implement incremental writing.
pub fn write_dimacs_header(target: &mut impl io::Write, header: DimacsHeader) -> io::Result<()> {
    writeln!(
        target,
        "p cnf {var_count} {clause_count}",
        var_count = header.var_count,
        clause_count = header.clause_count
    )
}

/// Write an iterator of clauses as headerless DIMACS CNF.
///
/// Can be used with [`write_dimacs_header`] to implement incremental writing.
pub fn write_dimacs_clauses(
    target: &mut impl io::Write,
    clauses: impl IntoIterator<Item = impl IntoIterator<Item = impl Borrow<Lit>>>,
) -> io::Result<()> {
    for clause in clauses.into_iter() {
        for lit in clause.into_iter() {
            itoa::write(&mut *target, lit.borrow().to_dimacs())?;
            target.write_all(b" ")?;
        }
        target.write_all(b"0\n")?;
    }
    Ok(())
}

/// Write a formula as DIMACS CNF.
///
/// Use [`write_dimacs_header`] and [`write_dimacs_clauses`] to implement incremental writing.
pub fn write_dimacs(target: &mut impl io::Write, formula: &CnfFormula) -> io::Result<()> {
    write_dimacs_header(
        &mut *target,
        DimacsHeader {
            var_count: formula.var_count(),
            clause_count: formula.len(),
        },
    )?;
    write_dimacs_clauses(&mut *target, formula.iter())
}

#[cfg(test)]
mod tests {
    use super::*;

    use anyhow::Error;
    use proptest::{test_runner::TestCaseError, *};

    use varisat_formula::{cnf::strategy::*, cnf_formula};

    #[test]
    fn odd_whitespace() -> Result<(), Error> {
        let parsed = DimacsParser::parse(
            b"p  cnf  4   3  \n  1  \n 2  3\n0 -4 0 2\nccomment  \n\n0\n\n" as &[_],
        )?;

        let expected = cnf_formula![
            1, 2, 3;
            -4;
            2;
        ];

        assert_eq!(parsed, expected);

        Ok(())
    }

    macro_rules! expect_error {
        ( $input:expr, $( $cases:tt )* ) => {
            match DimacsParser::parse($input as &[_]) {
                Ok(parsed) => panic!("Expexcted errror but got {:?}", parsed),
                Err(err) => match err.downcast_ref() {
                    Some(casted_err) => match casted_err {
                        $( $cases )*,
                        _ => panic!("Unexpected error {:?}", casted_err),
                    },
                    None => panic!("Unexpected error type {:?}", err),
                }
            }
        };
    }

    #[test]
    fn invalid_headers() {
        expect_error!(b"pcnf 1 3", ParserError::InvalidHeader { .. } => ());
        expect_error!(b"p notcnf 1 3", ParserError::InvalidHeader { .. } => ());
        expect_error!(b"p cnf 1", ParserError::InvalidHeader { .. } => ());
        expect_error!(b"p cnf 1 2 3", ParserError::InvalidHeader { .. } => ());
        expect_error!(b"p cnf foo bar", ParserError::InvalidHeader { .. } => ());
        expect_error!(b"p cnf -3 -6", ParserError::InvalidHeader { .. } => ());

        expect_error!(
            format!("p cnf {} 4", Var::max_var().to_dimacs() + 1).as_bytes(),
            ParserError::LiteralTooLarge { .. } => ()
        );
        DimacsParser::parse(format!("p cnf {} 0", Var::max_var().to_dimacs()).as_bytes()).unwrap();

        expect_error!(b"p cnf 4 18446744073709551616", ParserError::InvalidHeader { .. } => ());

        expect_error!(
            b"p cnf 1 2\np cnf 1 2\n",
            ParserError::UnexpectedInput { unexpected: 'p', .. } => ()
        );
    }

    #[test]
    fn invalid_header_data() {
        expect_error!(
            b"p cnf 1 1\n 2 0",
            ParserError::VarCount { var_count: 2, header_var_count: 1 } => ()
        );

        expect_error!(
            b"p cnf 10 1\n 1 0 0",
            ParserError::ClauseCount { clause_count: 2, header_clause_count: 1 } => ()
        );

        expect_error!(
            b"p cnf 10 4\n 1 0",
            ParserError::ClauseCount { clause_count: 1, header_clause_count: 4 } => ()
        );
    }

    #[test]
    fn syntax_errors() {
        expect_error!(
            b"1 2 ?foo",
            ParserError::UnexpectedInput { unexpected: '?', .. } => ()
        );

        expect_error!(
            b"1 2 - 3 0",
            ParserError::UnexpectedInput { unexpected: ' ', .. } => ()
        );

        expect_error!(
            b"1 2 -\n3 0",
            ParserError::UnexpectedInput { unexpected: '\n', .. } => ()
        );

        expect_error!(
            b"1 2 --3 0",
            ParserError::UnexpectedInput { unexpected: '-', .. } => ()
        );

        expect_error!(
            b"1 2-3 0",
            ParserError::UnexpectedInput { unexpected: '-', .. } => ()
        );
    }

    #[test]
    fn unterminated_clause() {
        expect_error!(
            b"1 2 3",
            ParserError::UnterminatedClause { .. } => ()
        );
    }

    #[test]
    fn literal_too_large() {
        expect_error!(
            format!("1 {} 2 0", Var::max_var().to_dimacs() + 1).as_bytes(),
            ParserError::LiteralTooLarge { .. } => ()
        );

        assert_eq!(
            DimacsParser::parse(format!("1 {} 2 0", Var::max_var().to_dimacs()).as_bytes())
                .unwrap(),
            cnf_formula![
                1, Var::max_var().to_dimacs(), 2;
            ]
        );
    }

    proptest! {

        #[test]
        fn roundtrip(input in cnf_formula(1..100usize, 0..1000, 0..10)) {
            let mut buf = vec![];

            write_dimacs(&mut buf, &input)?;

            let parsed = DimacsParser::parse(&buf[..]).map_err(|e| TestCaseError::fail(e.to_string()))?;

            prop_assert_eq!(parsed, input);
        }
    }
}
