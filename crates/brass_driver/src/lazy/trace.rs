//! Always-on observations of lazy compilation, printed only through tracing.

use std::time::Duration;

/// Work performed by one lazy run, including its runtime resolver.
///
/// The startup summary precedes entry into native code; the final summary is
/// emitted when the driver returns or explicitly terminates the process.
/// A native exit skips the final summary and Rust destructors. Runtime resolve
/// events remain available to account for resolutions after startup.
#[derive(Debug, Default)]
pub(crate) struct LazyCounters {
    demand_batches: u32,
    demanded_bodies: u32,
    demand_wait: Duration,
    mono_passes: u32,
    channel_refreshes: u32,
    lowering_appends: u32,
    lowering_rebuilds: u32,
    runtime_resolves: u32,
}

impl LazyCounters {
    /// Inspect demand-call and unchecked-body totals in coordination tests.
    #[cfg(test)]
    pub(super) fn demand_counts(&self) -> (u32, u32) {
        (self.demand_batches, self.demanded_bodies)
    }

    /// Record a demand call's elapsed time and its unchecked, distinct bodies
    /// after already-queued progress has been absorbed when settlement needs it.
    /// Every demand call counts as a batch, including already checked demands;
    /// these still traverse the demand protocol and contribute to `demand_wait`.
    pub(crate) fn record_demand(&mut self, bodies: usize, elapsed: Duration) {
        self.demand_batches += 1;
        self.demanded_bodies += bodies as u32;
        self.demand_wait += elapsed;
    }

    /// Count an attempted entry or runtime-instance monomorphization pass.
    pub(crate) fn record_mono_pass(&mut self) {
        self.mono_passes += 1;
    }

    /// Count a channel refresh, including refreshes with no changed entries.
    pub(crate) fn record_channel_refresh(&mut self) {
        self.channel_refreshes += 1;
    }

    /// Count successful function additions, including re-additions to a rebuild.
    /// In-place body refreshes and methods lowered by construction are excluded.
    pub(crate) fn record_lowering_appends(&mut self, bodies: usize) {
        self.lowering_appends += bodies as u32;
    }

    /// Count subset constructions, including the initial lowering.
    pub(crate) fn record_lowering_rebuild(&mut self) {
        self.lowering_rebuilds += 1;
    }

    /// Count resolver entries, including an already compiled address lookup.
    pub(crate) fn record_runtime_resolve(&mut self) {
        self.runtime_resolves += 1;
    }

    /// Emit the snapshot immediately before entering native execution.
    pub(crate) fn emit_startup(&self) {
        self.emit("startup");
    }

    /// Emit the final snapshot; native exits do not return to this boundary.
    pub(crate) fn emit_summary(&self) {
        self.emit("final");
    }

    fn emit(&self, phase: &str) {
        tracing::debug!(
            target: "brass::perf",
            phase,
            demand_batches = self.demand_batches,
            demanded_bodies = self.demanded_bodies,
            demand_wait_ms = self.demand_wait.as_secs_f64() * 1000.0,
            mono_passes = self.mono_passes,
            channel_refreshes = self.channel_refreshes,
            lowering_appends = self.lowering_appends,
            lowering_rebuilds = self.lowering_rebuilds,
            runtime_resolves = self.runtime_resolves,
            "lazy: summary"
        );
    }
}

impl Drop for LazyCounters {
    fn drop(&mut self) {
        self.emit_summary();
    }
}
