//! Solver configuration.
use varisat_macros::{ConfigUpdate, DocDefault};

/// Configurable parameters used during solving.
#[derive(DocDefault, ConfigUpdate)]
pub struct SolverConfig {
    /// Multiplicative decay for the VSIDS decision heuristic.
    ///
    /// Default: 0.95; Range: 0.5..1.0
    pub vsids_decay: f32,

    /// Multiplicative decay for clause activities.
    ///
    /// Default: 0.999; Range: 0.5..1.0
    pub clause_activity_decay: f32,

    /// Number of conflicts between local clause reductions.
    ///
    /// Default: 15000; Range: 1..
    pub reduce_locals_interval: u64,

    /// Number of conflicts between mid clause reductions.
    ///
    /// Default: 10000; Range: 1..
    pub reduce_mids_interval: u64,

    /// Scaling factor for luby sequence based restarts (number of conflicts).
    ///
    /// Default: 128; Range: 1..
    pub luby_restart_interval_scale: u64,
}
