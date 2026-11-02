//! Opt-in root co-check footprints (`brass::item_inventory=trace`). Observations
//! are evidence about actual walks, never absence certificates or selection.

use super::GlobalReadProvenance;
use crate::infer::Checker;
use brass_hir::{
    ItemKind, MethodBodyId, MethodInfo, Reason, SourceOrigin, Type, TypeInfo, TypeKind,
};
use std::collections::BTreeMap;

/// A root walk's shared projection, independent of memo admission and journals.
/// Only enabled tracing allocates it; nested replays supply qualified reads.
pub(in crate::infer) struct ItemObservation {
    id: Option<MethodBodyId>,
    owner: String,
    method: String,
    variant: Option<i32>,
    schemes_only: bool,
    declaration_candidate: bool,
    cells: Vec<(String, Type, Type)>,
    shapes: BTreeMap<u32, String>,
    returns: BTreeMap<(String, String), Type>,
    links: BTreeMap<(String, String), Vec<(Type, Type)>>,
}

impl Checker<'_> {
    /// Snapshot shared declaration/global cells before a root method walk.
    /// This never opens a production memo journal or changes its eligibility.
    #[inline]
    pub(in crate::infer) fn begin_item_inventory(
        &mut self,
        owner: &TypeInfo,
        method: &MethodInfo,
        variant: Option<i32>,
        schemes_only: bool,
    ) -> Option<Box<ItemObservation>> {
        if !tracing::enabled!(target: "brass::item_inventory", tracing::Level::TRACE) {
            return None;
        }
        Some(self.capture_item_inventory(owner, method, variant, schemes_only))
    }

    /// Capture an enabled root without touching production journals or counters.
    #[cold]
    #[inline(never)]
    fn capture_item_inventory(
        &mut self,
        owner: &TypeInfo,
        method: &MethodInfo,
        variant: Option<i32>,
        schemes_only: bool,
    ) -> Box<ItemObservation> {
        let mut cells = Vec::new();
        let mut add = |name: String, ty: &Type| {
            cells.push((name, ty.clone(), self.resolve(ty)));
        };
        for t in self.program.types.values() {
            let groups: Vec<_> = match &t.kind {
                TypeKind::Record { fields, methods } => vec![(String::new(), fields, methods)],
                TypeKind::Sum { variants } => variants
                    .iter()
                    .map(|v| (format!(".{}", v.name), &v.fields, &v.methods))
                    .collect(),
            };
            for (variant, fields, methods) in groups {
                for field in fields {
                    if let Some(ty) = &field.resolved_ty {
                        add(format!("{}.field{}:{}", t.symbol, variant, field.name), ty);
                    }
                }
                for m in methods.values() {
                    for p in &m.signature.params {
                        if let Some(ty) = &p.resolved_ty {
                            add(
                                format!(
                                    "{}.method{}:{}.{}",
                                    t.symbol, variant, m.signature.name, p.name
                                ),
                                ty,
                            );
                        }
                    }
                    if let Some(ty) = &m.signature.ret_ty {
                        add(
                            format!("{}.return{}:{}", t.symbol, variant, m.signature.name),
                            ty,
                        );
                    }
                }
            }
        }
        for f in self.program.functions.values() {
            for param in &f.signature.params {
                if let Some(ty) = &param.resolved_ty {
                    add(format!("function:{}.{}", f.symbol, param.name), ty);
                }
            }
            if let Some(ty) = &f.signature.ret_ty {
                add(format!("function:{}:return", f.symbol), ty);
            }
        }
        for (name, ty) in &self.function_returns {
            add(format!("function-return:{name}"), ty);
        }
        for ((owner, method), ty) in &self.co_method_returns {
            add(format!("co-return:{owner}.{method}"), ty);
        }
        for (owner, scheme) in &self.schemes {
            for (name, ty) in &scheme.fields {
                add(format!("scheme:{owner}.{name}"), ty);
            }
            for (name, method) in &scheme.methods {
                for (param, ty) in &method.params {
                    add(format!("scheme:{owner}.{name}.{param}"), ty);
                }
                add(format!("scheme:{owner}.{name}:return"), &method.ret);
            }
        }
        for (module, globals) in &self.global_defs {
            for (name, ty) in globals {
                add(format!("global:{}/{}", module.join("/"), name), ty);
            }
        }
        cells.sort_by(|a, b| a.0.cmp(&b.0));
        let inventory = self.method_inventory.as_mut().expect("enabled inventory");
        assert!(
            inventory.item_reads.is_none(),
            "root windows are not nested"
        );
        inventory.item_reads = Some(GlobalReadProvenance::default());
        inventory.item_closure = false;
        let shapes = cells
            .iter()
            .flat_map(|(_, ty, resolved)| {
                brass_hir::type_vars(ty)
                    .into_iter()
                    .chain(brass_hir::type_vars(resolved))
            })
            .map(|id| (id, format!("{:?}", self.shape_constraints.get(&id))))
            .collect();
        Box::new(ItemObservation {
            id: self.program.method_body_id(owner, method, variant),
            owner: owner.symbol.clone(),
            method: method.signature.name.clone(),
            variant,
            schemes_only,
            declaration_candidate: declaration_candidate(owner, method),
            cells,
            shapes,
            returns: self
                .method_returns
                .iter()
                .map(|(k, v)| (k.clone(), self.resolve(v)))
                .collect(),
            links: self
                .co_return_links
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
        })
    }

    /// Report writes and unresolved dependencies at the ordinary co-check boundary.
    /// A quiet observed walk is not proof of absence on another inference frame.
    #[inline]
    pub(in crate::infer) fn finish_item_inventory(
        &mut self,
        observation: Option<Box<ItemObservation>>,
    ) {
        let Some(observation) = observation else {
            return;
        };
        self.report_item_inventory(observation);
    }

    /// Format an enabled observation away from the ordinary body walk's stack.
    #[cold]
    #[inline(never)]
    fn report_item_inventory(&mut self, observation: Box<ItemObservation>) {
        let inventory = self.method_inventory.as_mut().expect("enabled inventory");
        let reads = inventory.item_reads.take().expect("balanced root window");
        let closure = inventory.item_closure;
        let changed_cells: Vec<_> = observation
            .cells
            .iter()
            .filter_map(|(name, ty, before)| {
                let after = self.resolve(ty);
                (after != *before).then_some((name, before, after))
            })
            .collect();
        let external_returns: Vec<_> = self
            .method_returns
            .iter()
            .filter(|((owner, _), _)| {
                owner != &observation.owner
                    && !owner.starts_with(&format!("{}.", observation.owner))
            })
            .filter_map(|(key, ty)| {
                let after = self.resolve(ty);
                (observation.returns.get(key) != Some(&after)).then(|| (key.clone(), after))
            })
            .collect();
        let external_links: Vec<_> = self
            .co_return_links
            .iter()
            .filter(|((owner, _), _)| owner != &observation.owner)
            .filter(|(key, links)| observation.links.get(*key) != Some(*links))
            .map(|(key, links)| (key.clone(), links.clone()))
            .collect();
        let changed_shapes: Vec<_> = observation
            .shapes
            .iter()
            .filter(|(id, before)| format!("{:?}", self.shape_constraints.get(id)) != **before)
            .collect();
        let open_reads = reads
            .reads
            .iter()
            .any(|(_, ty)| !brass_hir::is_fully_known(ty));
        tracing::trace!(target: "brass::item_inventory",
            id = ?observation.id, owner = observation.owner, method = observation.method,
            variant = ?observation.variant, schemes_only = observation.schemes_only,
            reason = ?Reason::SharedInference,
            candidate = observation.declaration_candidate, changed_cells = ?changed_cells,
            changed_shapes = ?changed_shapes, external_returns = ?external_returns, external_links = ?external_links,
            globals = ?reads.reads, untracked = reads.untracked, open_reads, closure,
            "check: item footprint");
    }

    /// Emit known roots only; explicit/implicit dependency closure belongs to
    /// selection, not to this inventory of work the checker actually performs.
    #[inline]
    pub(in crate::infer) fn observe_item_roots(&self) {
        if !tracing::enabled!(target: "brass::item_inventory", tracing::Level::TRACE) {
            return;
        }
        self.emit_item_roots();
    }

    /// Walk source metadata only when root tracing is enabled.
    #[cold]
    #[inline(never)]
    fn emit_item_roots(&self) {
        for init in &self.program.inits {
            let source = init.source.as_deref();
            tracing::trace!(target: "brass::item_inventory", module = ?init.path,
                source = ?source,
                id = ?source.and_then(|s| self.program.item_id(&init.path,
                    brass_hir::Span::new(s.base, s.base), ItemKind::Initializer)),
                reason = ?Reason::Initializer, "check: item root");
        }
        for t in self.program.types.values() {
            if self
                .program
                .module_source(&t.module, t.span)
                .is_some_and(|s| matches!(s.origin, SourceOrigin::Own(_)))
            {
                tracing::trace!(target: "brass::item_inventory",
                    id = ?self.program.item_id(&t.module, t.span, ItemKind::Type),
                    symbol = t.symbol, reason = ?Reason::Own, "check: item root");
            }
        }
        for f in self.program.functions.values() {
            if self
                .program
                .module_source(&f.module, f.decl.span)
                .is_some_and(|s| matches!(s.origin, SourceOrigin::Own(_)))
            {
                tracing::trace!(target: "brass::item_inventory",
                    id = ?self.program.item_id(&f.module, f.decl.span, ItemKind::Function),
                    symbol = f.symbol, reason = ?Reason::Own, "check: item root");
            }
        }
    }
}

/// Declaration-only inventory gate. Nominal closure and external effects must
/// still be certified before this candidate could ever be omitted.
fn declaration_candidate(owner: &TypeInfo, method: &MethodInfo) -> bool {
    let fields_closed = |fields: &[brass_hir::FieldInfo]| {
        fields.iter().all(|f| {
            f.resolved_ty
                .as_ref()
                .is_some_and(brass_hir::is_fully_known)
        })
    };
    owner.slots.is_empty()
        && match &owner.kind {
            TypeKind::Sum { variants } => variants.iter().all(|v| fields_closed(&v.fields)),
            TypeKind::Record { fields, .. } => {
                fields_closed(fields)
                    && method.signature.params.iter().all(|p| {
                        p.name == "self"
                            || p.resolved_ty
                                .as_ref()
                                .is_some_and(brass_hir::is_fully_known)
                    })
                    && method
                        .signature
                        .ret_ty
                        .as_ref()
                        .is_some_and(brass_hir::is_fully_known)
            }
        }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::infer::co_replay::{
        MethodInventory,
        snapshot::{EffectHistory, EffectSnapshot},
    };
    use std::rc::Rc;

    /// Root observations must preserve all channels, links, diagnostics and
    /// counters even when child calls start walking and later replay a memo.
    #[test]
    fn root_window_is_read_only_and_collects_nested_provenance() {
        let source = "const FLAG = true\nfun leaf() -> bool { return FLAG }\ntype Box = {}\nfun Box.test(self) -> bool { let a = leaf()\nlet b = leaf()\nreturn a && b }";
        let (p, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
            source: None,
            path: vec!["main".into()],
            is_prelude: false,
            ast: brass_parser::parse(source).unwrap(),
        }]);
        assert!(errors.is_empty());
        let mut seed = Checker::new(&p, Rc::new(brass_typesys::RowInfo::analyze(&p)));
        seed.precompute_global_bindings();
        seed.precompute_returns();
        seed.co_checking = true;
        seed.current_module = vec!["main".into()];
        seed.current_co_method = Some(("Box".into(), "test".into()));
        let mut plain = EffectSnapshot::fork(&seed);
        let mut observed = EffectSnapshot::fork(&seed);
        observed.method_inventory = Some(Box::new(MethodInventory::default()));
        let owner = &p.types["Box"];
        let TypeKind::Record { methods, .. } = &owner.kind else {
            panic!()
        };
        let method = &methods["test"];
        let observation = observed.capture_item_inventory(owner, method, None, false);
        let run = |c: &mut Checker<'_>| {
            let mut scopes = c.signature_scopes(&method.signature.params);
            c.check_block_with_self(
                method.decl.body.as_ref().unwrap(),
                &mut scopes,
                method.signature.ret_ty.as_ref(),
                "Box",
            );
        };
        run(&mut plain);
        run(&mut observed);
        let reads = observed
            .method_inventory
            .as_ref()
            .unwrap()
            .item_reads
            .as_ref()
            .unwrap();
        assert!(!reads.untracked);
        assert_eq!(reads.reads.len(), 1);
        assert_eq!(reads.reads[0].0.name, "FLAG");
        assert_eq!(reads.reads[0].0.module, ["main"]);
        assert_eq!(reads.reads[0].1, Type::Bool);
        observed.finish_item_inventory(Some(observation));
        let mut a = EffectHistory::new(&seed);
        let mut b = EffectHistory::new(&seed);
        a.boundary(&plain);
        b.boundary(&observed);
        EffectSnapshot::capture(&plain, &[], &Type::Bool, &a)
            .compare(&EffectSnapshot::capture(&observed, &[], &Type::Bool, &b))
            .unwrap();
        assert!(
            plain.stats.co_hits > 0,
            "the root must include a nested replay"
        );
        assert_eq!(plain.elaborations, observed.elaborations);
        assert_eq!(plain.depth_capped, observed.depth_capped);
        assert_eq!(
            format!("{:?}", plain.stats),
            format!("{:?}", observed.stats)
        );
    }
}
