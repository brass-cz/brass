//! Opt-in timings for selection work, separate from checker operations.

use std::time::{Duration, Instant};

/// Read the clock only while selector-cost observation is enabled.
pub(super) fn start() -> Option<Instant> {
    tracing::enabled!(target: "brass::item_cost", tracing::Level::DEBUG).then(Instant::now)
}

/// Report one inclusive operation; nested certificate time is reported separately.
pub(super) fn finish(phase: &'static str, start: Option<Instant>) {
    if let Some(start) = start {
        elapsed(phase, start.elapsed());
    }
}

/// Emit an already measured component without another clock read.
pub(super) fn elapsed(phase: &'static str, elapsed: Duration) {
    tracing::debug!(target: "brass::item_cost", phase, ms = elapsed.as_secs_f64() * 1000.0, "item: cost");
}
