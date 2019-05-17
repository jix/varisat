use proptest::{prelude::*, *};

use rand::distributions::Bernoulli;
use rand::seq::SliceRandom;

use crate::cnf::CnfFormula;
use crate::lit::Lit;

/// Generate small hard unsat instances.
///
/// Implementation of http://www.cs.qub.ac.uk/~i.spence/sgen/ but with random partitions
pub fn sgen_unsat_formula(
    blocks: impl Strategy<Value = usize>,
) -> impl Strategy<Value = CnfFormula> {
    blocks.prop_flat_map(|blocks| {
        collection::vec(bool::ANY, blocks * 4 + 1).prop_perturb(|polarity, mut rng| {
            let mut clauses: Vec<Vec<Lit>> = vec![];
            let mut lits = polarity
                .into_iter()
                .enumerate()
                .map(|(index, polarity)| Lit::from_index(index, polarity))
                .collect::<Vec<_>>();

            for &invert in [false, true].iter() {
                lits.shuffle(&mut rng);
                for block in lits.chunks_exact(4) {
                    for a in 0..4 {
                        for b in 0..a {
                            for c in 0..b {
                                let mut clause =
                                    vec![block[a] ^ invert, block[b] ^ invert, block[c] ^ invert];
                                clause.shuffle(&mut rng);
                                clauses.push(clause);
                            }
                        }
                    }
                }
                let &lit_a = lits.last().unwrap();
                for b in 0..4 {
                    for c in 0..b {
                        let mut clause = vec![lit_a ^ invert, lits[b] ^ invert, lits[c] ^ invert];
                        clause.shuffle(&mut rng);
                        clauses.push(clause);
                    }
                }
            }

            clauses.shuffle(&mut rng);
            CnfFormula::from(clauses)
        })
    })
}

/// Generate a sat instance.
///
/// This generates a random full assignment and then only generates clauses compatible with that
/// assignment.
pub fn sat_formula(
    vars: impl Strategy<Value = usize>,
    clause_count: impl Strategy<Value = usize>,
    density: impl Strategy<Value = f64>,
    polarity_dist: impl Strategy<Value = f64>,
) -> impl Strategy<Value = CnfFormula> {
    (vars, clause_count, density, polarity_dist).prop_flat_map(
        |(vars, clause_count, density, polarity_dist)| {
            let density = Bernoulli::new(density);
            let polarity_dist = Bernoulli::new(polarity_dist);

            collection::vec(bool::ANY, vars).prop_perturb(move |polarity, mut rng| {
                let mut clauses: Vec<Vec<Lit>> = vec![];
                let lits = polarity
                    .into_iter()
                    .enumerate()
                    .map(|(index, polarity)| Lit::from_index(index, polarity))
                    .collect::<Vec<_>>();

                for _ in 0..clause_count {
                    let &fixed_lit = lits.choose(&mut rng).unwrap();
                    let mut clause = vec![fixed_lit];
                    for &lit in lits.iter() {
                        if lit != fixed_lit && rng.sample(density) {
                            clause.push(lit ^ rng.sample(polarity_dist));
                        }
                    }
                    clause.shuffle(&mut rng);
                    clauses.push(clause);
                }

                clauses.shuffle(&mut rng);
                CnfFormula::from(clauses)
            })
        },
    )
}

/// Generates a conditional pigeon hole principle formula.
pub fn conditional_pigeon_hole(
    columns: impl Strategy<Value = usize>,
    extra_rows: impl Strategy<Value = usize>,
) -> impl Strategy<Value = (Vec<Lit>, usize, CnfFormula)> {
    (columns, extra_rows).prop_flat_map(|(columns, extra_rows)| {
        let rows = columns + extra_rows;
        let vars = (columns + 1) * rows;

        collection::vec(bool::ANY, vars).prop_perturb(move |polarity, mut rng| {
            let mut clauses: Vec<Vec<Lit>> = vec![];
            let lits = polarity
                .into_iter()
                .enumerate()
                .map(|(index, polarity)| Lit::from_index(index, polarity))
                .collect::<Vec<_>>();

            for i in 1..columns + 1 {
                for j in 0..rows {
                    for k in 0..j {
                        let mut clause = [lits[i * rows + j], lits[i * rows + k]];
                        clause.shuffle(&mut rng);
                        clauses.push(clause[..].to_owned());
                    }
                }
            }

            for j in 0..rows {
                let mut clause: Vec<_> = (0..columns + 1).map(|i| !lits[i * rows + j]).collect();
                clause.shuffle(&mut rng);
                clauses.push(clause[..].to_owned());
            }

            clauses.shuffle(&mut rng);
            (lits[0..rows].to_owned(), columns, CnfFormula::from(clauses))
        })
    })
}
