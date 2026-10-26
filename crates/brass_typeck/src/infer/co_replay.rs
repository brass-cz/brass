//! The co-check effects a call-site body walk must preserve.
//!
//! Return links belong to the enclosing co-method; global reads belong to the
//! analysis. These helpers are the only writers of those two inventories.

use super::Checker;
use brass_hir::Type;

mod admission;
mod methods;
mod provenance;
/// Opt-in method dependency windows, independent of memo admission.
pub(super) use methods::MethodInventory;
/// Shared-state certificate required by closed method co entries.
pub(super) use methods::MethodMemoDependencies;
/// Exact qualified value reads retained by ordinary and co memo entries.
pub(super) use provenance::GlobalReadProvenance;

mod validation;
/// Opt-in nested observations for exact replay-versus-walk checks.
pub(super) use validation::CoEffects;

/// Differential observation of independent test checkers and their streams.
#[cfg(test)]
pub(super) mod snapshot;
#[cfg(test)]
mod tests;

impl Checker<'_> {
    /// Describe retained co entries only when inventory tracing is enabled.
    /// Shared observations count once per entry, not once per allocation.
    pub(super) fn observe_co_inventory(&self) {
        if !tracing::enabled!(target: "brass::perf", tracing::Level::TRACE) {
            return;
        }
        let mut entries = 0;
        let mut observations = 0;
        let mut links = 0;
        let mut reads = 0;
        for (key, entry) in &self.elaboration_memo {
            if matches!(key.flavor, super::journal::MemoFlavor::CoCheck { .. }) {
                entries += 1;
                let (all, co_links, co_reads) = entry.observation_counts();
                observations += all;
                links += co_links;
                reads += co_reads;
            }
        }
        tracing::trace!(target: "brass::perf",
            method_entries = self.elaboration_memo.values().filter(|e| e.method_dependencies.is_some()).count(),
            provenance_entries = self.elaboration_memo.values().filter(|e| e.global_reads.is_some()).count(),
            qualified_reads = self.elaboration_memo.values().filter_map(|e| e.global_reads.as_ref()).map(|p| p.reads.len()).sum::<usize>(),
            entry_bytes = std::mem::size_of::<super::journal::ElaborationMemoEntry>(),
            "check: method memo inventory");
        tracing::trace!(target: "brass::perf", entries, observations, links, reads,
            observation_bytes = std::mem::size_of::<super::journal::ElaborationJournalEntry>(),
            "check: co memo inventory");
    }

    /// Admit free-function co-check reuse outside numeric probes.
    /// Receiver functions also use the free-function elaborator, but remain
    /// methods for admission. Concrete inputs are checked on the resolved key.
    pub(super) fn co_memo_eligible(&self, symbol: &str) -> bool {
        !self.co_memo_suspended && !self.numeric.probing && self.co_free_function(symbol)
    }

    /// Exclude receiver declarations even when lowered as function symbols.
    pub(super) fn co_free_function(&self, symbol: &str) -> bool {
        self.program
            .functions
            .get(symbol)
            .is_some_and(|info| info.decl.recv.is_none())
    }

    /// Retain the ordinary key's full identity while separating co-check
    /// observations. Open inputs remain on the body-walk path.
    pub(super) fn co_memo_context(
        &self,
        mut context: Option<super::journal::ElaborationMemoContext>,
    ) -> Option<super::journal::ElaborationMemoContext> {
        if self.co_checking {
            let key = &mut context.as_mut()?.key;
            if !key
                .receiver
                .iter()
                .chain(key.args.iter())
                .chain(key.scheme_inputs.iter().flatten())
                .all(brass_hir::is_fully_known)
            {
                return None;
            }
            key.flavor = super::journal::MemoFlavor::CoCheck {
                has_root: self.current_co_method.is_some(),
            };
        }
        context
    }

    /// Count co-check lookups as a subset of total memo lookups. The opt-in
    /// event attributes reuse to a callable without formatting disabled keys.
    pub(super) fn observe_co_lookup(
        &mut self,
        key: &super::journal::ElaborationMemoKey,
        hit: bool,
    ) {
        if let super::journal::MemoFlavor::CoCheck { has_root } = key.flavor {
            if hit {
                self.stats.co_hits += 1;
            } else {
                self.stats.co_misses += 1;
            }
            tracing::trace!(
                target: "brass::perf",
                callable = key.callable,
                has_root,
                method = key.receiver.is_some() || key.callable.strip_prefix("fn:").is_some_and(|symbol| !self.co_free_function(symbol.split(":numeric-layout=").next().unwrap())),
                hit,
                "check: co memo"
            );
        }
    }

    /// Append a unifiable return pair to the current co-method, preserving order
    /// and duplicates. A rootless co-check has no scheme to attach links to.
    pub(super) fn record_co_return_link(&mut self, left: Type, right: Type) {
        if let Some(key) = self.current_co_method.clone() {
            if self.validate_co_link(&left, &right) {
                return;
            }
            if !self.elaboration_journals.is_empty() || self.method_inventory.is_some() {
                self.journal_elaboration(super::journal::ElaborationJournalEntry::CoReturnLink {
                    left: left.clone(),
                    right: right.clone(),
                });
            }
            self.co_return_links
                .entry(key)
                .or_default()
                .push((left, right));
        }
    }

    /// Remember a global read whose provisional type the co-check depended on.
    /// Repeated reads are idempotent; initializer settlement consults this set.
    pub(super) fn record_co_global_read(&mut self, name: &str) {
        if self.validate_co_global(name) {
            return;
        }
        if !self.elaboration_journals.is_empty() || self.method_inventory.is_some() {
            self.journal_elaboration(super::journal::ElaborationJournalEntry::CoGlobalRead {
                name: name.to_owned(),
            });
        }
        self.co_global_reads.insert(name.to_owned());
    }

    /// Count an admitted body walk, excluding recursion, depth and budget
    /// fallbacks. Eligible memo misses are counted separately from bypasses.
    /// Trace fields are evaluated only when the perf trace target is enabled.
    pub(super) fn observe_body_walk(&mut self, callable: &str, has_memo_key: bool) {
        if self.co_checking && !has_memo_key {
            self.stats.co_walks += 1;
        }
        if !has_memo_key && tracing::enabled!(target: "brass::perf", tracing::Level::TRACE) {
            tracing::trace!(
                target: "brass::perf",
                callable,
                reason = if self.co_checking && (callable.starts_with("method:") || callable.strip_prefix("fn:").is_some_and(|symbol| !self.co_free_function(symbol))) { "method" }
                    else if self.numeric.probing || self.co_memo_suspended { "numeric_probe" }
                    else if !self.type_test_holes.is_empty() { "type_test_probe" }
                    else if self.co_checking { "open_frame" }
                    else { "ineligible_key" },
                co_check = self.co_checking,
                numeric_probe = self.numeric.probing,
                type_test_probe = !self.type_test_holes.is_empty(),
                speculation_depth = self.speculation_depth,
                "check: memo bypass"
            );
        }
    }
}
