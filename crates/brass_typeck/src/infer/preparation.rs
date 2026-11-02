//! Coverage queries at the boundary between context preparation and body checking.

use super::{Checker, Program};
use crate::reachability::AnalysisView;
use std::rc::Rc;

impl Checker<'_> {
    /// Install a selected request for this numeric attempt; genuine seed coverage
    /// is supplied separately through `apply_seed`.
    pub(super) fn select_preparation(&mut self, view: Option<&AnalysisView>) {
        self.preparation = view.cloned().map(Rc::new);
    }

    /// Supply newly selected static facts before an affected body can publish.
    /// Const-call facts are replaced as one complete sidecar, never inferred absent.
    pub(super) fn refresh_selected_facts(&mut self, seed: Option<&super::ContextTables>) {
        let Some(view) = &self.preparation else {
            return;
        };
        let (errors, calls) = crate::static_checks(
            self.program,
            crate::AnalysisModules {
                seed,
                view: Some(view),
            },
        );
        self.errors.extend(errors);
        self.const_calls = Rc::new(calls);
    }

    /// Grow a priority body's execution closure without inventing checked coverage.
    /// Shared producers and keyed possibilities must already be closed at entry.
    pub(super) fn select_demand(&mut self, symbol: &str) -> bool {
        let Some(view) = &mut self.preparation else {
            return false;
        };
        let Some(body) = view.functions.get(symbol).cloned() else {
            return false;
        };
        if view.selection.body_roots.contains(&body) {
            return false;
        }
        let index = self
            .selection_index
            .get_or_insert_with(|| Rc::new(crate::reachability::ItemIndex::new(self.program)));
        let expanded = crate::reachability::Reachability::extend_root(
            index,
            &view.selection,
            crate::reachability::ItemKey::Body(body),
            brass_hir::Reason::Demand,
        );
        debug_assert!(
            expanded.type_roots.is_subset(&view.selection.type_roots),
            "runtime demand discovered an unprepared shared owner: {symbol}"
        );
        debug_assert!(
            expanded
                .body_roots
                .difference(&view.selection.body_roots)
                .all(|id| !matches!(id, crate::reachability::BodyId::Method(_))),
            "runtime demand discovered a method outside pre-gate closure: {symbol}"
        );
        Rc::make_mut(view).set_selection(expanded.into());
        self.precompute_returns();
        self.refresh_selected_facts(None);
        true
    }

    /// A shared co-check is skipped only when covered or outside the selected request.
    pub(super) fn prepares_method(&self, qualifier: &str, name: &str, preliminary: bool) -> bool {
        if self.preparation.is_none() && self.item_seed.is_none() {
            return true;
        }
        let key = (qualifier.to_owned(), name.to_owned());
        if let Some(view) = &self.preparation
            && !view
                .methods
                .get(&key)
                .is_some_and(|id| view.selection.body_roots.contains(id))
        {
            return false;
        }
        if let Some(view) = &self.item_seed {
            let id = view.methods.get(&key);
            if id.is_some_and(|id| view.coverage.co_checks.contains(id)) {
                return false;
            }
            debug_assert!(
                self.method_returns.contains_key(&key),
                "entry co-check requires a prepared return: {key:?}"
            );
            debug_assert!(
                id.is_none_or(|id| !view.coverage.bodies.contains(id)),
                "uncovered co-check claimed body coverage"
            );
            tracing::debug!(target: "brass::item_preparation", qualifier, name, preliminary, context = id.is_some_and(|id| view.catalog.contains(id)), "item: co fallback");
        }
        true
    }

    /// Gate body-only work without restricting the declaration catalog.
    pub(super) fn selects_body(&self, span: brass_parser::Span) -> bool {
        self.preparation
            .as_ref()
            .is_none_or(|view| view.selects_body(span))
    }

    /// Record a real shared-frame check, independently of scheme seed work.
    pub(super) fn covered_method(&mut self, qualifier: &str, name: &str) {
        if let Some(view) = &mut self.preparation {
            let view = Rc::make_mut(view);
            let id = view.methods[&(qualifier.into(), name.into())].clone();
            view.coverage_mut().co_checks.insert(id);
        }
    }

    /// Only requested owners can supply inferred schemes in a partial context.
    pub(super) fn prepares_scheme(&self, symbol: &str) -> bool {
        self.preparation
            .as_ref()
            .is_none_or(|view| view.selection.type_roots.contains(&view.types[symbol]))
    }

    /// An existing scheme is reusable only with its shared-component certificate.
    pub(super) fn seeded_scheme(&self, symbol: &str, module: &[String]) -> bool {
        self.item_seed.as_ref().map_or_else(
            || self.seeded_module(module),
            |view| {
                let covered = view.types.get(symbol).is_some_and(|id| view.shared.schemes.contains(id));
                if !covered {
                    tracing::debug!(target: "brass::item_preparation", symbol, "item: scheme fallback");
                }
                covered
            },
        )
    }

    /// Globals are reused only for a completed initializer, never a partial module.
    pub(super) fn seeded_globals(&self, module: &[String]) -> bool {
        self.item_seed.as_ref().map_or_else(
            || self.seeded_module(module),
            |view| {
                view.initializers
                    .get(module)
                    .is_some_and(|id| view.shared.initializers.contains(id))
            },
        )
    }

    /// Check that the partial seed's claimed return work has a corresponding table.
    pub(super) fn assert_item_seed(&self, program: &Program) {
        if let Some(view) = &self.item_seed {
            debug_assert!(
                view.coverage.bodies.is_subset(&view.coverage.returns),
                "ordinary body coverage requires completed return preparation"
            );
            for (symbol, id) in view.functions.iter() {
                debug_assert!(
                    !view.coverage.returns.contains(id)
                        || self.function_returns.contains_key(symbol),
                    "missing covered function return: {symbol}"
                );
            }
            for (key, id) in view.methods.iter() {
                debug_assert!(
                    !view.coverage.returns.contains(id) || self.method_returns.contains_key(key),
                    "missing covered method return: {key:?}"
                );
            }
            debug_assert!(view.shared.schemes.iter().all(|id| view.types.iter().any(
                |(symbol, tid)| tid == id
                    && program.types.contains_key(symbol)
                    && self.schemes.contains_key(symbol)
            )));
        }
    }
}
