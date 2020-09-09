//! Variable mapping and metadata.

use hashbrown::HashSet;

use partial_ref::{partial, PartialRef};

use varisat_formula::{Lit, Var};
use varisat_internal_proof::ProofStep;

use crate::context::{parts::*, set_var_count, Context};
use crate::decision;
use crate::proof;

pub mod data;
pub mod var_map;

use data::{SamplingMode, VarData};
use var_map::{VarBiMap, VarBiMapMut, VarMap};

/// Variable mapping and metadata.
pub struct Variables {
    /// Bidirectional mapping from user variables to global variables.
    ///
    /// Initially this is the identity mapping. This ensures that in the non-assumptions setting the
    /// map from used user variables to global variables is the identity. This is a requirement for
    /// generating proofs in non-native formats. Those proofs are not aware of variable renaming,
    /// but are restricted to the non-incremental setting, so this works out.
    ///
    /// This is also requried for native proofs, as they assume that the mapping during the initial
    /// load is the identity.
    global_from_user: VarBiMap,
    /// Bidirectional mapping from global variables to user variables.
    ///
    /// This starts with the empty mapping, so only used variables are allocated.
    solver_from_global: VarBiMap,
    /// User variables that were explicitly hidden by the user.
    user_freelist: HashSet<Var>,
    /// Global variables that can be recycled without increasing the global_watermark.
    global_freelist: HashSet<Var>,
    /// Solver variables that are unused and can be recycled.
    solver_freelist: HashSet<Var>,

    /// Variable metadata.
    ///
    /// Indexed by global variable indices.
    var_data: Vec<VarData>,
}

impl Default for Variables {
    fn default() -> Variables {
        Variables {
            global_from_user: VarBiMap::default(),
            solver_from_global: VarBiMap::default(),
            user_freelist: Default::default(),
            global_freelist: Default::default(),
            solver_freelist: Default::default(),

            var_data: vec![],
        }
    }
}

impl Variables {
    /// Number of allocated solver variables.
    pub fn solver_watermark(&self) -> usize {
        self.global_from_solver().watermark()
    }

    /// Number of allocated global variables.
    pub fn global_watermark(&self) -> usize {
        self.var_data.len()
    }

    /// Number of allocated global variables.
    pub fn user_watermark(&self) -> usize {
        self.global_from_user().watermark()
    }

    /// Iterator over all user variables that are in use.
    pub fn user_var_iter<'a>(&'a self) -> impl Iterator<Item = Var> + 'a {
        let global_from_user = self.global_from_user.fwd();
        (0..self.global_from_user().watermark())
            .map(Var::from_index)
            .filter(move |&user_var| global_from_user.get(user_var).is_some())
    }

    /// Iterator over all global variables that are in use.
    pub fn global_var_iter<'a>(&'a self) -> impl Iterator<Item = Var> + 'a {
        (0..self.global_watermark())
            .map(Var::from_index)
            .filter(move |&global_var| !self.var_data[global_var.index()].deleted)
    }

    /// The user to global mapping.
    pub fn global_from_user(&self) -> &VarMap {
        &self.global_from_user.fwd()
    }

    /// Mutable user to global mapping.
    pub fn global_from_user_mut(&mut self) -> VarBiMapMut {
        self.global_from_user.fwd_mut()
    }

    /// The global to solver mapping.
    pub fn solver_from_global(&self) -> &VarMap {
        &self.solver_from_global.fwd()
    }

    /// Mutable global to solver mapping.
    pub fn solver_from_global_mut(&mut self) -> VarBiMapMut {
        self.solver_from_global.fwd_mut()
    }

    /// The global to user mapping.
    pub fn user_from_global(&self) -> &VarMap {
        &self.global_from_user.bwd()
    }

    /// Mutable global to user mapping.
    pub fn user_from_global_mut(&mut self) -> VarBiMapMut {
        self.global_from_user.bwd_mut()
    }

    /// The solver to global mapping.
    pub fn global_from_solver(&self) -> &VarMap {
        &self.solver_from_global.bwd()
    }

    /// Mutable  solver to global mapping.
    pub fn global_from_solver_mut(&mut self) -> VarBiMapMut {
        self.solver_from_global.bwd_mut()
    }

    /// Get an existing solver var for a user var.
    pub fn existing_solver_from_user(&self, user: Var) -> Var {
        let global = self
            .global_from_user()
            .get(user)
            .expect("no existing global var for user var");
        let solver = self
            .solver_from_global()
            .get(global)
            .expect("no existing solver var for global var");
        solver
    }

    /// Get an existing user var from a solver var.
    pub fn existing_user_from_solver(&self, solver: Var) -> Var {
        let global = self
            .global_from_solver()
            .get(solver)
            .expect("no existing global var for solver var");
        let user = self
            .user_from_global()
            .get(global)
            .expect("no existing user var for global var");
        user
    }

    /// Mutable reference to the var data for a global variable.
    pub fn var_data_global_mut(&mut self, global: Var) -> &mut VarData {
        if self.var_data.len() <= global.index() {
            self.var_data.resize(global.index() + 1, VarData::default());
        }
        &mut self.var_data[global.index()]
    }

    /// Mutable reference to the var data for a solver variable.
    pub fn var_data_solver_mut(&mut self, solver: Var) -> &mut VarData {
        let global = self
            .global_from_solver()
            .get(solver)
            .expect("no existing global var for solver var");
        &mut self.var_data[global.index()]
    }

    /// Var data for a global variable.
    pub fn var_data_global(&self, global: Var) -> &VarData {
        &self.var_data[global.index()]
    }

    /// Check if a solver var is mapped to a global var
    pub fn solver_var_present(&self, solver: Var) -> bool {
        self.global_from_solver().get(solver).is_some()
    }

    /// Get an unmapped global variable.
    pub fn next_unmapped_global(&self) -> Var {
        self.global_freelist
            .iter()
            .next()
            .cloned()
            .unwrap_or_else(|| Var::from_index(self.global_watermark()))
    }

    /// Get an unmapped global variable.
    pub fn next_unmapped_solver(&self) -> Var {
        self.solver_freelist
            .iter()
            .next()
            .cloned()
            .unwrap_or_else(|| Var::from_index(self.solver_watermark()))
    }

    /// Get an unmapped user variable.
    pub fn next_unmapped_user(&self) -> Var {
        self.user_freelist
            .iter()
            .next()
            .cloned()
            .unwrap_or_else(|| Var::from_index(self.user_watermark()))
    }
}

/// Maps a user variable into a global variable.
///
/// If no matching global variable exists a new global variable is allocated.
pub fn global_from_user<'a>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP, mut VariablesP),
    user: Var,
    require_sampling: bool,
) -> Var {
    let variables = ctx.part_mut(VariablesP);

    if user.index() > variables.user_watermark() {
        // TODO use a batch proof step for this?
        for index in variables.user_watermark()..user.index() {
            global_from_user(ctx.borrow(), Var::from_index(index), false);
        }
    }

    let variables = ctx.part_mut(VariablesP);

    match variables.global_from_user().get(user) {
        Some(global) => {
            if require_sampling
                && variables.var_data[global.index()].sampling_mode != SamplingMode::Sample
            {
                panic!("witness variables cannot be constrained");
            }
            global
        }
        None => {
            // Can we add an identity mapping?
            let global = match variables.var_data.get(user.index()) {
                Some(var_data) if var_data.deleted => user,
                None => user,
                _ => variables.next_unmapped_global(),
            };

            *variables.var_data_global_mut(global) = VarData::user_default();

            variables.global_from_user_mut().insert(global, user);
            variables.global_freelist.remove(&global);
            variables.user_freelist.remove(&user);

            proof::add_step(
                ctx.borrow(),
                false,
                &ProofStep::UserVarName {
                    global,
                    user: Some(user),
                },
            );

            global
        }
    }
}

/// Maps an existing global variable to a solver variable.
///
/// If no matching solver variable exists a new one is allocated.
pub fn solver_from_global<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut AnalyzeConflictP,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ImplGraphP,
        mut ProofP<'a>,
        mut SolverStateP,
        mut TmpFlagsP,
        mut VariablesP,
        mut VsidsP,
        mut WatchlistsP,
    ),
    global: Var,
) -> Var {
    let variables = ctx.part_mut(VariablesP);

    debug_assert!(!variables.var_data[global.index()].deleted);

    match variables.solver_from_global().get(global) {
        Some(solver) => solver,
        None => {
            let solver = variables.next_unmapped_solver();

            let old_watermark = variables.global_from_solver().watermark();

            variables.solver_from_global_mut().insert(solver, global);
            variables.solver_freelist.remove(&solver);

            let new_watermark = variables.global_from_solver().watermark();

            if new_watermark > old_watermark {
                set_var_count(ctx.borrow(), new_watermark);
            }

            initialize_solver_var(ctx.borrow(), solver, global);

            proof::add_step(
                ctx.borrow(),
                false,
                &ProofStep::SolverVarName {
                    global,
                    solver: Some(solver),
                },
            );

            solver
        }
    }
}

/// Maps a user variable to a solver variable.
///
/// Allocates global and solver variables as requried.
pub fn solver_from_user<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut AnalyzeConflictP,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ImplGraphP,
        mut ProofP<'a>,
        mut SolverStateP,
        mut TmpFlagsP,
        mut VariablesP,
        mut VsidsP,
        mut WatchlistsP,
    ),
    user: Var,
    require_sampling: bool,
) -> Var {
    let global = global_from_user(ctx.borrow(), user, require_sampling);
    solver_from_global(ctx.borrow(), global)
}

/// Allocates a currently unused user variable.
///
/// This is either a user variable above any user variable used so far, or a user variable that was
/// previously hidden by the user.
pub fn new_user_var<'a>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP, mut VariablesP),
) -> Var {
    let variables = ctx.part_mut(VariablesP);
    let user_var = variables.next_unmapped_user();
    global_from_user(ctx.borrow(), user_var, false);
    user_var
}

/// Maps a slice of user lits to solver lits using [`solver_from_user`].
pub fn solver_from_user_lits<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut AnalyzeConflictP,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ImplGraphP,
        mut ProofP<'a>,
        mut SolverStateP,
        mut TmpFlagsP,
        mut VariablesP,
        mut VsidsP,
        mut WatchlistsP,
    ),
    solver_lits: &mut Vec<Lit>,
    user_lits: &[Lit],
    require_sampling: bool,
) {
    solver_lits.clear();
    solver_lits.extend(user_lits.iter().map(|user_lit| {
        user_lit.map_var(|user_var| solver_from_user(ctx.borrow(), user_var, require_sampling))
    }))
}

/// Changes the sampling mode of a global variable.
///
/// If the mode is changed to hidden, an existing user mapping is automatically removed.
///
/// If the mode is changed from hidden, a new user mapping is allocated and the user variable is
/// returned.
pub fn set_sampling_mode<'a>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP, mut VariablesP),
    global: Var,
    mode: SamplingMode,
) -> Option<Var> {
    let variables = ctx.part_mut(VariablesP);

    let var_data = &mut variables.var_data[global.index()];

    assert!(!var_data.deleted);

    if var_data.assumed {
        panic!("cannot change sampling mode of assumption variable")
    }

    let previous_mode = var_data.sampling_mode;

    if previous_mode == mode {
        return None;
    }

    var_data.sampling_mode = mode;

    let mut result = None;

    if mode != SamplingMode::Hide {
        proof::add_step(
            ctx.borrow(),
            false,
            &ProofStep::ChangeSamplingMode {
                var: global,
                sample: mode == SamplingMode::Sample,
            },
        );
    }
    let variables = ctx.part_mut(VariablesP);

    if previous_mode == SamplingMode::Hide {
        let user = variables.next_unmapped_user();
        variables.user_from_global_mut().insert(user, global);
        variables.user_freelist.remove(&user);

        proof::add_step(
            ctx.borrow(),
            false,
            &ProofStep::UserVarName {
                global,
                user: Some(user),
            },
        );

        result = Some(user);
    } else if mode == SamplingMode::Hide {
        if let Some(user) = variables.user_from_global_mut().remove(global) {
            variables.user_freelist.insert(user);
        }

        proof::add_step(
            ctx.borrow(),
            false,
            &ProofStep::UserVarName { global, user: None },
        );

        delete_global_if_unused(ctx.borrow(), global);
    }

    result
}

/// Turns all hidden vars into witness vars and returns them.
pub fn observe_internal_vars<'a>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP, mut VariablesP),
) -> Vec<Var> {
    let mut result = vec![];
    let mut variables = ctx.part_mut(VariablesP);
    for global_index in 0..variables.global_watermark() {
        let global = Var::from_index(global_index);
        let var_data = &variables.var_data[global.index()];
        if !var_data.deleted && var_data.sampling_mode == SamplingMode::Hide {
            let user = set_sampling_mode(ctx.borrow(), global, SamplingMode::Witness).unwrap();
            result.push(user);
            variables = ctx.part_mut(VariablesP);
        }
    }
    result
}

/// Initialize a newly allocated solver variable
pub fn initialize_solver_var(
    mut ctx: partial!(
        Context,
        mut AssignmentP,
        mut ImplGraphP,
        mut VsidsP,
        VariablesP
    ),
    solver: Var,
    global: Var,
) {
    let (variables, mut ctx) = ctx.split_part(VariablesP);
    let data = &variables.var_data[global.index()];

    // This recovers the state of a variable that has a known value and was already propagated. This
    // is important so that when new clauses containing this variable are added, load_clause knows
    // to reenqueue the assignment.
    ctx.part_mut(AssignmentP).set_var(solver, data.unit);
    if data.unit.is_some() {
        ctx.part_mut(ImplGraphP).update_removed_unit(solver);
    }
    decision::initialize_var(ctx.borrow(), solver, data.unit.is_none());

    // TODO unhiding beyond unit clauses
}

/// Remove a solver var.
///
/// If the variable is isolated and hidden, the global variable is also removed.
pub fn remove_solver_var<'a>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP, mut VariablesP, mut VsidsP),
    solver: Var,
) {
    decision::remove_var(ctx.borrow(), solver);

    let variables = ctx.part_mut(VariablesP);

    let global = variables
        .global_from_solver_mut()
        .remove(solver)
        .expect("no existing global var for solver var");

    variables.solver_freelist.insert(solver);

    proof::add_step(
        ctx.borrow(),
        false,
        &ProofStep::SolverVarName {
            global,
            solver: None,
        },
    );

    delete_global_if_unused(ctx.borrow(), global);
}

/// Delete a global variable if it is unused
fn delete_global_if_unused<'a>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP, mut VariablesP),
    global: Var,
) {
    let variables = ctx.part_mut(VariablesP);

    if variables.user_from_global().get(global).is_some() {
        return;
    }

    if variables.solver_from_global().get(global).is_some() {
        return;
    }

    let data = &mut variables.var_data[global.index()];

    assert!(data.sampling_mode == SamplingMode::Hide);

    if !data.isolated {
        return;
    }

    data.deleted = true;

    proof::add_step(ctx.borrow(), false, &ProofStep::DeleteVar { var: global });

    // TODO deletion of unit clauses isn't supported by most DRAT checkers, needs an extra
    // variable mapping instead.

    ctx.part_mut(VariablesP).global_freelist.insert(global);
}

#[cfg(test)]
mod tests {
    use proptest::{collection, prelude::*};

    use varisat_formula::test::{sat_formula, sgen_unsat_formula};
    use varisat_formula::{ExtendFormula, Var};

    use crate::solver::Solver;

    #[test]
    #[should_panic(expected = "cannot change sampling mode of assumption variable")]
    fn cannot_hide_assumed_vars() {
        let mut solver = Solver::new();

        let (x, y, z) = solver.new_lits();

        solver.assume(&[x, y, z]);
        solver.hide_var(x.var());
    }

    #[test]
    #[should_panic(expected = "cannot change sampling mode of assumption variable")]
    fn cannot_witness_assumed_vars() {
        let mut solver = Solver::new();

        let (x, y, z) = solver.new_lits();

        solver.assume(&[x, y, z]);
        solver.witness_var(x.var());
    }

    proptest! {
        #[test]
        fn sgen_unsat_hidden_with_sat(
            unsat_formula in sgen_unsat_formula(1..7usize),
            sat_formula in sat_formula(4..20usize, 10..100usize, 0.05..0.2, 0.9..1.0),
        ) {
            use std::cmp::max;

            let mut solver = Solver::new();

            solver.enable_self_checking();

            let cond = Var::from_index(max(unsat_formula.var_count(), sat_formula.var_count()));

            let mut tmp = vec![];

            for clause in unsat_formula.iter() {
                tmp.clear();
                tmp.extend_from_slice(&clause);
                tmp.push(cond.negative());
                solver.add_clause(&tmp);
            }

            for i in 0..unsat_formula.var_count() {
                solver.hide_var(Var::from_index(i));
            }

            solver.add_formula(&sat_formula);

            prop_assert_eq!(solver.solve().ok(), Some(true));

            solver.add_clause(&[cond.positive()]);

            prop_assert_eq!(solver.solve().ok(), Some(false));
        }

        #[test]
        fn sgen_sat_many_hidden_observe_internal(
            sat_formulas in collection::vec(
                sat_formula(4..20usize, 10..100usize, 0.05..0.2, 0.9..1.0),
                1..10,
            )
        ) {
            let mut solver = Solver::new();

            solver.enable_self_checking();

            for formula in sat_formulas {
                solver.add_formula(&formula);

                let new_vars = solver.observe_internal_vars();

                for i in 0..formula.var_count() {
                    solver.hide_var(Var::from_index(i));
                }

                for var in new_vars {
                    solver.hide_var(var);
                }
            }

            prop_assert_eq!(solver.solve().ok(), Some(true));
        }
    }
}
