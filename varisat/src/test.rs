use proptest::{prelude::*, *};

use rand::distributions::Bernoulli;
use rand::seq::SliceRandom;

use crate::cnf::CnfFormula;
use crate::lit::{Lit, Var};

/// Generate small hard unsat instances.
///
/// Implementation of http://www.cs.qub.ac.uk/~i.spence/sgen/ but with random partitions
pub fn sgen_unsat_formula(
    blocks: impl Strategy<Value = usize>,
) -> impl Strategy<Value = CnfFormula> {
    blocks.prop_flat_map(|blocks| {
        collection::vec(bool::ANY, blocks * 4 + 1).prop_perturb(|negate, mut rng| {
            let mut clauses: Vec<Vec<Lit>> = vec![];
            let mut lits = negate
                .into_iter()
                .enumerate()
                .map(|(index, negate)| Lit::from_var(Var::from_index(index), negate))
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

            collection::vec(bool::ANY, vars).prop_perturb(move |negate, mut rng| {
                let mut clauses: Vec<Vec<Lit>> = vec![];
                let lits = negate
                    .into_iter()
                    .enumerate()
                    .map(|(index, negate)| Lit::from_var(Var::from_index(index), negate))
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
