//! Counts owned by committed checker states, independent of trace filtering.

use super::Checker;

/// Observations for an analysis, including scheme seeding and numeric retries.
/// Probe clones own private counts; discarded probe work is excluded, as it is
/// from the checker's elaboration budget and depth-cap totals. Memo hits count
/// successful lookups even when memo validation also re-elaborates the body.
#[derive(Clone, Debug, Default)]
pub(super) struct ElaborationStats {
    /// Eligible memo lookups that found an entry.
    pub(super) memo_hits: u64,
    /// Eligible memo lookups that found no entry; ineligible calls are excluded.
    pub(super) memo_misses: u64,
    /// Co-check body walks that bypassed the memo, excluding recursion and
    /// depth/budget fallbacks. Discarded probe clones do not contribute.
    pub(super) co_walks: u64,
    /// Successful co-check lookups, included in memo_hits. Validation hits
    /// still count even when the body is subsequently walked for comparison.
    pub(super) co_hits: u64,
    /// Eligible co-check lookups without an entry, included in memo_misses.
    pub(super) co_misses: u64,
    /// Free-function dedicated passes, excluding initializers, methods, and
    /// call-site elaborations. Skipped seeded functions do not count.
    pub(super) dedicated_passes: u64,
    cap_hits: u64,
    elaborations: u64,
}

impl ElaborationStats {
    /// Add a completed checker's observations, reusing its operational totals.
    pub(super) fn record_checker(&mut self, checker: &Checker<'_>) {
        checker.observe_co_inventory();
        self.memo_hits += checker.stats.memo_hits;
        self.memo_misses += checker.stats.memo_misses;
        self.co_walks += checker.stats.co_walks;
        self.co_hits += checker.stats.co_hits;
        self.co_misses += checker.stats.co_misses;
        self.dedicated_passes += checker.stats.dedicated_passes;
        self.cap_hits += checker.depth_capped;
        self.elaborations += checker.elaborations;
    }

    /// Emit one event per analysis, after all its attempts have completed.
    pub(super) fn emit_summary(&self) {
        tracing::debug!(
            target: "brass::perf",
            memo_hits = self.memo_hits,
            memo_misses = self.memo_misses,
            co_walks = self.co_walks,
            co_hits = self.co_hits,
            co_misses = self.co_misses,
            cap_hits = self.cap_hits,
            elaborations = self.elaborations,
            dedicated_passes = self.dedicated_passes,
            "check: summary"
        );
    }
}
