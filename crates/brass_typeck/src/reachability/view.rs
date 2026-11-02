//! Separate requested preparation from facts actually established by a checker.
//! A partial context never grants module-wide or ordinary-body coverage.

use super::{BodyId, CheckSelection, index::item_id};
use brass_hir::{ItemId, ItemKind, MethodBodyId, Program, TypeKind};
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::sync::Arc;

/// Completed item work, independent of module names and storage qualification.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ItemCoverage {
    /// Returns settled by the ordinary light-pass fixpoint.
    pub returns: HashSet<BodyId>,
    /// Methods checked in their shared declaration frame.
    pub co_checks: HashSet<BodyId>,
    /// Ordinary dedicated bodies checked, not merely elaborated at a call site.
    pub bodies: HashSet<BodyId>,
}

/// Shared producers whose complete preparation may be reused as a unit.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SharedComponentCoverage {
    /// Record schemes built after all selected shared producers completed.
    pub schemes: HashSet<ItemId>,
    /// Loaded initializer sequences whose globals were prepared and checked.
    pub initializers: HashSet<ItemId>,
}

/// A selection and its established coverage projected onto one HIR identity space.
/// Projection allocates lookup tables once; checker loops use storage identities.
#[derive(Debug, Default, PartialEq)]
pub struct AnalysisView {
    /// Immutable requested work shared by checker forks; membership never grants coverage.
    pub(crate) selection: Arc<CheckSelection>,
    /// Context-only requests establish shared preparation without dedicated passes.
    pub(crate) preparation_only: bool,
    /// Source declarations mapped to their distinct callable checking contexts.
    declarations: Arc<HashMap<brass_parser::Span, Vec<BodyId>>>,
    /// Integer span membership, rebuilt only when the selected request grows.
    selected_declarations: Arc<HashSet<brass_parser::Span>>,
    /// Item facts established by a preceding analysis.
    pub coverage: Arc<ItemCoverage>,
    /// Shared components established by a preceding analysis.
    pub shared: Arc<SharedComponentCoverage>,
    /// Bodies present in the context catalog, including unprepared siblings.
    pub(crate) catalog: Arc<HashSet<BodyId>>,
    /// Function symbols mapped to stable source bodies.
    pub(crate) functions: Arc<HashMap<String, BodyId>>,
    /// Qualified method return keys mapped to variant-specific bodies.
    pub(crate) methods: Arc<HashMap<(String, String), BodyId>>,
    /// Nominal storage symbols mapped to stable declarations.
    pub(crate) types: Arc<HashMap<String, ItemId>>,
    /// Loaded namespaces mapped to initialization identities.
    pub(crate) initializers: Arc<HashMap<Vec<String>, ItemId>>,
}

impl Clone for AnalysisView {
    fn clone(&self) -> Self {
        let started = super::cost::start();
        let cloned = Self {
            selection: self.selection.clone(),
            preparation_only: self.preparation_only,
            declarations: self.declarations.clone(),
            selected_declarations: self.selected_declarations.clone(),
            coverage: self.coverage.clone(),
            shared: self.shared.clone(),
            catalog: self.catalog.clone(),
            functions: self.functions.clone(),
            methods: self.methods.clone(),
            types: self.types.clone(),
            initializers: self.initializers.clone(),
        };
        super::cost::finish("coverage-clone", started);
        cloned
    }
}

impl AnalysisView {
    /// Project stable source IDs onto `program` without re-running reachability.
    pub fn new(
        program: &Program,
        selection: CheckSelection,
        coverage: ItemCoverage,
        shared: SharedComponentCoverage,
    ) -> Self {
        Self::with_selection(program, Arc::new(selection), coverage, shared)
    }

    /// Project a shared immutable request onto a second HIR identity space.
    /// Context and entry keep the same request but establish separate coverage.
    pub fn with_selection(
        program: &Program,
        selection: Arc<CheckSelection>,
        coverage: ItemCoverage,
        shared: SharedComponentCoverage,
    ) -> Self {
        let started = super::cost::start();
        let functions: HashMap<_, _> = program
            .functions
            .iter()
            .map(|(symbol, f)| {
                (
                    symbol.clone(),
                    BodyId::Function(item_id(program, &f.module, f.decl.span, ItemKind::Function)),
                )
            })
            .collect();
        let mut methods = HashMap::default();
        let mut types = HashMap::default();
        for t in program.types.values() {
            let id = item_id(program, &t.module, t.span, ItemKind::Type);
            types.insert(t.symbol.clone(), id.clone());
            let groups = match &t.kind {
                TypeKind::Record { methods, .. } => vec![(None, t.symbol.clone(), methods)],
                TypeKind::Sum { variants } => variants
                    .iter()
                    .map(|v| (Some(v.tag), format!("{}.{}", t.symbol, v.name), &v.methods))
                    .collect(),
            };
            for (variant, qualifier, group) in groups {
                for (name, m) in group {
                    let mid =
                        program
                            .method_body_id(t, m, variant)
                            .unwrap_or_else(|| MethodBodyId {
                                owner: id.clone(),
                                module: id.module.clone(),
                                offset: m.decl.span.lo,
                                variant,
                                name: m.signature.name.clone(),
                            });
                    methods.insert((qualifier.clone(), name.clone()), BodyId::Method(mid));
                }
            }
        }
        let initializers = program
            .inits
            .iter()
            .map(|init| {
                let base = init.source.as_ref().map_or(0, |s| s.base);
                (
                    init.path.clone(),
                    item_id(
                        program,
                        &init.path,
                        brass_parser::Span::new(base, base),
                        ItemKind::Initializer,
                    ),
                )
            })
            .collect();
        let catalog = functions
            .values()
            .chain(methods.values())
            .cloned()
            .collect();
        let mut declarations: HashMap<_, Vec<_>> = HashMap::default();
        for (symbol, f) in &program.functions {
            declarations
                .entry(f.decl.span)
                .or_default()
                .push(functions[symbol.as_str()].clone());
        }
        for t in program.types.values() {
            let groups = match &t.kind {
                TypeKind::Record { methods, .. } => vec![(t.symbol.clone(), methods)],
                TypeKind::Sum { variants } => variants
                    .iter()
                    .map(|v| (format!("{}.{}", t.symbol, v.name), &v.methods))
                    .collect(),
            };
            for (qualifier, group) in groups {
                for (name, m) in group {
                    declarations
                        .entry(m.decl.span)
                        .or_default()
                        .push(methods[&(qualifier.clone(), name.clone())].clone());
                }
            }
        }
        let selected_declarations = declarations
            .iter()
            .filter(|(_, ids)| ids.iter().any(|id| selection.body_roots.contains(id)))
            .map(|(span, _)| *span)
            .collect();
        super::cost::finish("coverage", started);
        Self {
            preparation_only: false,
            declarations: Arc::new(declarations),
            selected_declarations: Arc::new(selected_declarations),
            catalog: Arc::new(catalog),
            selection,
            coverage: Arc::new(coverage),
            shared: Arc::new(shared),
            functions: Arc::new(functions),
            methods: Arc::new(methods),
            types: Arc::new(types),
            initializers: Arc::new(initializers),
        }
    }

    /// Source bodies eligible for checking and lowering. This is a request,
    /// not evidence of a completed pass; declarations remain in the catalog.
    pub fn body_spans(&self) -> &Arc<HashSet<brass_parser::Span>> {
        &self.selected_declarations
    }

    /// Project appended generated declarations and close their dependencies before
    /// continuation checks. Existing shared inputs must have been selected before
    /// entry; generated bodies do not establish coverage merely by being present.
    pub fn with_generated(
        &self,
        program: &brass_hir::Program,
        generated: &[brass_hir::GeneratedDecl],
    ) -> Self {
        let mut view = self.clone();
        view.preparation_only = false;
        let mut roots = HashSet::default();
        for generated in generated {
            let info = program
                .types
                .values()
                .find(|t| t.name == generated.receiver && t.module == generated.module)
                .expect("generated owner");
            let groups = match &info.kind {
                TypeKind::Record { methods, .. } => vec![(None, info.symbol.clone(), methods)],
                TypeKind::Sum { variants } => variants
                    .iter()
                    .map(|v| {
                        (
                            Some(v.tag),
                            format!("{}.{}", info.symbol, v.name),
                            &v.methods,
                        )
                    })
                    .collect(),
            };
            for (variant, qualifier, group) in groups {
                let method = &group[&generated.decl.name];
                let id = program
                    .method_body_id(info, method, variant)
                    .unwrap_or_else(|| {
                        let owner = view.types[&info.symbol].clone();
                        MethodBodyId {
                            module: owner.module.clone(),
                            owner,
                            offset: method.decl.span.lo,
                            variant,
                            name: method.signature.name.clone(),
                        }
                    });
                let body = BodyId::Method(id);
                assert!(
                    Arc::make_mut(&mut view.methods)
                        .insert((qualifier, method.signature.name.clone()), body.clone())
                        .is_none(),
                    "generated body already projected"
                );
                Arc::make_mut(&mut view.catalog).insert(body.clone());
                Arc::make_mut(&mut view.declarations)
                    .entry(method.decl.span)
                    .or_default()
                    .push(body.clone());
                roots.insert(body);
            }
        }
        let extra = roots.iter().cloned().map(super::ItemKey::Body);
        let expanded = self
            .selection
            .continuation
            .as_ref()
            .expect("keyed selection has a settled continuation")
            .append(program, &view.selection, generated, extra);
        debug_assert!(
            expanded.type_roots.is_subset(&self.selection.type_roots),
            "generated dependency requires an owner outside the pre-gate closure"
        );
        debug_assert!(
            expanded
                .body_roots
                .difference(&self.selection.body_roots)
                .all(|id| roots.contains(id)),
            "generated dependency outside the pre-gate body closure"
        );
        view.set_selection(expanded.into());
        view
    }

    /// The immutable selected request; it does not claim completed coverage.
    pub fn selection(&self) -> &Arc<CheckSelection> {
        &self.selection
    }

    /// Replace a request and rebuild integer span membership as one operation.
    pub(crate) fn set_selection(&mut self, selection: Arc<CheckSelection>) {
        self.selected_declarations = Arc::new(
            self.declarations
                .iter()
                .filter(|(_, ids)| ids.iter().any(|id| selection.body_roots.contains(id)))
                .map(|(span, _)| *span)
                .collect(),
        );
        self.selection = selection;
    }

    /// Mutate established coverage without copying read-only checker forks.
    pub(crate) fn coverage_mut(&mut self) -> &mut ItemCoverage {
        Arc::make_mut(&mut self.coverage)
    }

    /// Whether any checking context of a source body is selected. Declaration
    /// metadata remains available even when this predicate is false.
    pub fn selects_body(&self, declaration: brass_parser::Span) -> bool {
        self.selected_declarations.contains(&declaration)
    }

    /// Keep catalog diagnostics and diagnostics of selected bodies only. A sum
    /// method source is reported if any of its variant contexts is selected.
    pub fn reports(&self, owner: &brass_hir::diagnostics::DiagnosticOwner) -> bool {
        use brass_hir::diagnostics::DiagnosticOwner;
        match owner {
            DiagnosticOwner::Catalog | DiagnosticOwner::Initializer(_) => true,
            DiagnosticOwner::Function(id) => self
                .selection
                .body_roots
                .contains(&BodyId::Function(id.clone())),
            DiagnosticOwner::Method(ids) => ids.iter().any(|id| {
                self.selection
                    .body_roots
                    .contains(&BodyId::Method(id.clone()))
            }),
        }
    }

    /// Remove coverage belonging to a dirty module/importer closure. Selection
    /// remains a request; removed facts cannot be reclaimed by retaining a module.
    pub(crate) fn retain(&mut self, program: &Program, keep: &HashSet<Vec<String>>) {
        let functions: HashSet<_> = self
            .functions
            .iter()
            .filter(|(symbol, _)| keep.contains(&program.functions[*symbol].module))
            .map(|(_, id)| id.clone())
            .collect();
        let types: HashSet<_> = self
            .types
            .iter()
            .filter(|(symbol, _)| keep.contains(&program.types[*symbol].module))
            .map(|(_, id)| id.clone())
            .collect();
        let retained = |id: &BodyId| match id {
            BodyId::Function(_) => functions.contains(id),
            BodyId::Method(m) => types.contains(&m.owner),
            BodyId::Initializer(_) => false,
        };
        self.coverage_mut().returns.retain(retained);
        self.coverage_mut().co_checks.retain(retained);
        self.coverage_mut().bodies.retain(retained);
        Arc::make_mut(&mut self.shared)
            .schemes
            .retain(|id| types.contains(id));
        let inits: HashSet<_> = self
            .initializers
            .iter()
            .filter(|(module, _)| keep.contains(*module))
            .map(|(_, id)| id.clone())
            .collect();
        Arc::make_mut(&mut self.shared)
            .initializers
            .retain(|id| inits.contains(id));
    }
}
