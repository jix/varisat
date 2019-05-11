//! Solver configuration.
use varisat_macros::{ConfigUpdate, DocDefault};

/// Configurable parameters used during solving.
#[derive(DocDefault, ConfigUpdate)]
pub struct SolverConfig {
    /// Multiplicative decay for the VSIDS decision heuristic.
    ///
    /// [default: 0.95]  [range: 0.5..1.0]
    pub vsids_decay: f32,

    /// Multiplicative decay for clause activities.
    ///
    /// [default: 0.999]  [range: 0.5..1.0]
    pub clause_activity_decay: f32,

    /// Number of conflicts between local clause reductions.
    ///
    /// [default: 15000]  [range: 1..]
    pub reduce_locals_interval: u64,

    /// Number of conflicts between mid clause reductions.
    ///
    /// [default: 10000]  [range: 1..]
    pub reduce_mids_interval: u64,

    /// Scaling factor for luby sequence based restarts (number of conflicts).
    ///
    /// [default: 128]  [range: 1..]
    pub luby_restart_interval_scale: u64,
}
