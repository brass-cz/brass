//! Differential co-effect observation, enabled only for memo validation.

use super::super::Checker;
use super::GlobalReadProvenance;
use brass_hir::Type;
use std::collections::BTreeSet;

/// One validation window's ordered links and idempotent global dependencies.
/// Replay windows collect effects without applying them; walk windows observe
/// the actual writes, including nested calls, so validation never doubles links.
#[derive(Clone, Default)]
pub(in crate::infer) struct CoEffects {
    /// Whether these effects substitute for writes during the validation replay.
    replay: bool,
    /// Return relations in their actual application order, including duplicates.
    links: Vec<(Type, Type)>,
    /// All global reads, including globals already present before the window.
    globals: BTreeSet<String>,
    /// Qualified types at reads, independent of the reporting names.
    dependencies: GlobalReadProvenance,
}

impl CoEffects {
    /// Dry replay observations must never leak into a surrounding actual walk.
    pub(in crate::infer) fn is_replay(&self) -> bool {
        self.replay
    }
}

impl Checker<'_> {
    /// Open a co-only validation window. Ordinary memo checks need no observer.
    pub(in crate::infer) fn begin_co_validation(&mut self, replay: bool) {
        self.co_validation.push(CoEffects {
            replay,
            ..CoEffects::default()
        });
    }

    /// Close the innermost replay or walk window without changing checker state.
    pub(in crate::infer) fn finish_co_validation(&mut self) -> CoEffects {
        self.co_validation.pop().expect("balanced co validation")
    }

    /// Observe a link in the innermost dry replay, or in every enclosing actual
    /// walk. A nested validation replay must not appear in its parent's walk.
    pub(super) fn validate_co_link(&mut self, left: &Type, right: &Type) -> bool {
        if let Some(probe) = self.co_validation.last_mut()
            && probe.replay
        {
            probe.links.push((left.clone(), right.clone()));
            return true;
        }
        for probe in &mut self.co_validation {
            probe.links.push((left.clone(), right.clone()));
        }
        false
    }

    /// Observe every read, rather than a set difference that could hide reads
    /// of globals already present. Return true only for a dry validation replay.
    pub(super) fn validate_co_global(&mut self, name: &str) -> bool {
        if let Some(probe) = self.co_validation.last_mut()
            && probe.replay
        {
            probe.globals.insert(name.to_owned());
            return true;
        }
        for probe in &mut self.co_validation {
            probe.globals.insert(name.to_owned());
        }
        false
    }

    /// Observe exact dependency reads with the same dry-replay boundary as links.
    pub(in crate::infer) fn validate_global_provenance(
        &mut self,
        reads: &GlobalReadProvenance,
    ) -> bool {
        if let Some(probe) = self.co_validation.last_mut()
            && probe.replay
        {
            probe.dependencies.extend(reads);
            return true;
        }
        for probe in &mut self.co_validation {
            probe.dependencies.extend(reads);
        }
        false
    }

    /// Compare the effects using one canonical variable namespace for the
    /// return and every link endpoint, preserving aliases across all of them.
    /// A capped validation walk is checked by the caller's existing cap guard.
    pub(in crate::infer) fn assert_co_validation(
        &self,
        callable: &str,
        replay: CoEffects,
        walk: CoEffects,
        replayed: &Type,
        returned: &Type,
    ) {
        let pack = |ret: &Type, effects: &CoEffects| {
            Type::Tuple(
                std::iter::once(ret.clone())
                    .chain(
                        effects
                            .links
                            .iter()
                            .flat_map(|(a, b)| [a.clone(), b.clone()]),
                    )
                    .collect(),
            )
        };
        debug_assert_eq!(
            self.canonical_memo_check_return(&pack(replayed, &replay)),
            self.canonical_memo_check_return(&pack(returned, &walk)),
            "co return links differ for {callable}"
        );
        debug_assert_eq!(
            replay.globals, walk.globals,
            "co global reads differ for {callable}"
        );
        let method = callable.starts_with("method:") || !self.co_free_function(callable);
        if method {
            debug_assert_eq!(
                replay.dependencies, walk.dependencies,
                "co qualified dependencies differ for {callable}"
            );
        }
        tracing::trace!(target: "brass::memo_check", callable,
            method,
            links = walk.links.len(),
            globals = walk.globals.len(), "check: co replay validated");
    }
}
