use std::collections::HashSet;

use varisat::lit::Lit;
use varisat::solver::Solver;

macro_rules! test_cnf {
    ($name:ident, $result:expr) => {
        #[test]
        fn $name() {
            let cnf = include_bytes!(concat!("cnfs/", stringify!($name), ".cnf"));
            let mut solver = Solver::new();
            solver.enable_self_checking();
            let formula = varisat::dimacs::DimacsParser::parse(&cnf[..]).expect("parsing failed");
            solver.add_formula(&formula);
            let result = $result;
            assert_eq!(solver.solve().expect("solve failed"), result);
            if result {
                let model: HashSet<Lit> = solver.model().unwrap().into_iter().collect();
                for clause in formula.iter() {
                    assert!(clause.iter().any(|&lit| model.contains(&lit)));
                }
            }
        }
    };
}

test_cnf!(sgen1_unsat_57_0, false);
test_cnf!(sgen1_sat_90_0, true);
