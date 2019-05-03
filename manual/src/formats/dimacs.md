# DIMACS CNF

The DIMACS CNF format is a textual representation of a formula in [conjunctive
normal form][cnf]. A formula in conjunctive normal form is a conjunction
(logical and) of a set of clauses. Each clause is a disjunction (logical or) of
a set of literals. A literal is a variable or a negation of a variable. DIMACS
CNF uses positive integers to represent variables and their negation to
represent the corresponding negated variable. This convention is also used for
all textual input and output in Varisat.

There are several variations and extensions of the DIMACS CNF format. Varisat
tries to accept any variation commonly found. Currently no extensions are
supported.

DIMACS CNF is a textual format. Any line that begins with the character `c` is
considered a comment. Some other parsers require comments to start with `c `
and/or support comments only at the beginning of a file. Varisat supports them
anywhere in the file.

A DIMACS file begins with a header line of the form `p cnf <variables>
<clauses>`. Where `<variables>` and `<clauses>` are replaced with decimal
numbers indicating the number of variables and clauses in the formula.

Varisat does not require a header line. If it is missing, it will infer the
number of clauses and variables. If a header line is present, though, the
formula must have the exact number of clauses and may not use variables
represented by a number larger than indicated.

Following the header line are the clauses of the formula. The clauses are
encoded as a sequence of decimal numbers separated by spaces and newlines. For
each clause the contained literals are listed followed by a `0`. Usually each
clause is listed on a separate line, using spaces between each of the literals
and the final zero. Sometimes long clauses use multiple lines. Varisat will
accept any combination of spaces and newlines as separators, including multiple
clauses on the same line.

As an example the formula (x ∨ y ∨ ¬z) ∧ (¬y ∨ z) could be encoded as this:

```cnf
p cnf 3 2
1 2 -3 0
-2 3 0
```

The [simplified DIMACS CNF format][simplified-dimacs] used by the
yearly SAT competitions is a subset of the format parsed by Varisat.

[cnf]: https://en.wikipedia.org/wiki/Conjunctive_normal_form
[simplified-dimacs]: https://web.archive.org/web/20190325181937/https://www.satcompetition.org/2009/format-benchmarks2009.html
