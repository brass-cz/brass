//! Final diagnostic certificates and conservative free-function dependency closure.

use brass_hir::{Program, Type, TypeKind};
use brass_mir::LoweringRegion;
use brass_parser::ast::{Block, Expr, Stmt, StrSeg};
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

use super::{BodySpans, LazyState};

/// Syntactic reference edges, including function values and nested closures.
/// Unknown dispatch and global values are excluded rather than guessed. Name
/// shadowing can add conservative edges, but cannot remove a real dependency.
pub(super) struct RegionGraph {
    /// Callees by canonical caller symbol.
    edges: HashMap<String, HashSet<String>>,
    /// Bodies with dispatch outside this free-function certificate.
    opaque: HashSet<String>,
    /// Draining cannot publish a new warning or reflective discovery early.
    can_drain: bool,
}

impl RegionGraph {
    /// Collect all reference edges without elaborating bodies or changing channels.
    pub(super) fn new(
        program: &Program,
        completed: &HashSet<String>,
        selected: Option<&HashSet<brass_parser::Span>>,
    ) -> Self {
        let mut graph = Self {
            edges: HashMap::default(),
            opaque: HashSet::default(),
            can_drain: true,
        };
        for (symbol, function) in &program.functions {
            if selected.is_some_and(|spans| !spans.contains(&function.decl.span)) {
                continue;
            }
            let mut edges = HashSet::default();
            // Keep implicit method dispatch and result conversions outside the
            // certificate. Open frames may forward values through free calls,
            // but cannot perform arithmetic that could negotiate a user method.
            let mut opaque = !matches!(
                function.decl.body.stmts.as_slice(),
                [Stmt::Return(Some(_), _)]
            ) || function
                .signature
                .params
                .iter()
                .filter_map(|p| p.resolved_ty.as_ref())
                .any(|ty| !scalar(ty))
                || function
                    .signature
                    .ret_ty
                    .as_ref()
                    .is_some_and(|ty| !scalar(ty));
            let open_arguments = function
                .signature
                .params
                .iter()
                .any(|p| p.resolved_ty.is_none());
            let mut propagations = 0;
            let mut raises = false;
            visit_block(&function.decl.body, &mut |expr| match expr {
                Expr::Ident(name, _) => {
                    if let Some(callee) = program.resolve_function(&function.module, name) {
                        edges.insert(callee.symbol.clone());
                    } else if !function.decl.params.iter().any(|p| p.name == *name) {
                        opaque = true;
                    }
                }
                Expr::Call(callee, _, _) => {
                    raises |= matches!(&**callee, Expr::Ident(name, _) if name == "error");
                    if !matches!(&**callee, Expr::Ident(name, _)
                            if !function.decl.params.iter().any(|p| p.name == *name)
                            && program.resolve_function(&function.module, name).is_some())
                    {
                        opaque = true;
                    }
                }
                Expr::ErrorProp(..) => {
                    propagations += 1;
                    opaque = true;
                }
                Expr::Unary(..) | Expr::Binary(..) => opaque |= open_arguments,
                Expr::Str(parts, _) => {
                    opaque |= parts.iter().any(|part| matches!(part, StrSeg::Expr(_)))
                }
                // A closure parameter can shadow a free-function name. Its
                // eventual call frame is outside this syntactic certificate;
                // still walk its body so all exclusion edges are retained.
                Expr::Closure(..) => opaque = true,
                Expr::Int(..) | Expr::Float(..) | Expr::Bool(..) | Expr::Null(..) => {}
                _ => opaque = true,
            });
            // The checker's only body warning requires an unannotated return
            // and both nullable propagation and an error source. Excluding
            // mixed candidates preserves warning text and print order.
            if !completed.contains(symbol)
                && function.decl.ret.is_none()
                && (propagations >= 2 || (propagations != 0 && raises))
            {
                tracing::debug!(target: "brass::perf", %symbol, "lazy: possible completion warning");
                graph.can_drain = false;
            }
            if brass_hir::keyed_return(function.decl.ret.as_ref()) {
                // Free-function infer returns are not reflective methods;
                // their open return shape is outside this region certificate.
                opaque = true;
            }
            if opaque {
                graph.opaque.insert(symbol.clone());
            }
            graph.edges.insert(symbol.clone(), edges);
        }
        // Reflective templates can be discovered by a background caller whose
        // diagnostic spans are not yet known. Keep the whole stream on demand.
        for info in program.types.values() {
            let methods: Vec<_> = match &info.kind {
                TypeKind::Record { methods, .. } => methods.values().collect(),
                TypeKind::Sum { variants } => {
                    variants.iter().flat_map(|v| v.methods.values()).collect()
                }
            };
            if methods.iter().any(|m| {
                selected.is_none_or(|spans| spans.contains(&m.decl.span))
                    && brass_hir::keyed_return(m.decl.ret.as_ref())
            }) {
                tracing::debug!(target: "brass::perf", symbol = %info.symbol, "lazy: reflective completion template");
                graph.can_drain = false;
            }
        }
        graph
    }

    /// Whether finishing the stream early preserves warning and keyed boundaries.
    pub(super) fn can_drain(&self) -> bool {
        self.can_drain
    }

    /// Certify checked minus every transitive caller of a bad body, after Finished.
    /// Only the portion referenced from already-needed roots is bulk lowered;
    /// the region does not itself make those bodies needed.
    pub(super) fn certify(&self, program: &Program, lazy: &LazyState) -> LoweringRegion {
        assert!(lazy.finished, "region requires terminal diagnostics");
        let bodies = BodySpans::new(program);
        let bad = self
            .opaque
            .iter()
            .cloned()
            .chain(
                program
                    .functions
                    .keys()
                    .filter(|s| !lazy.checked_fns.contains(*s))
                    .cloned(),
            )
            .chain(
                lazy.held
                    .iter()
                    .filter_map(|error| bodies.owner(error.span).map(str::to_owned)),
            )
            .collect();
        self.closed_region(bad, &lazy.needed)
    }

    /// Remove reverse-reachable bad bodies and restrict to needed-root reachability.
    fn closed_region(&self, mut bad: HashSet<String>, roots: &HashSet<String>) -> LoweringRegion {
        let mut callers: HashMap<&str, Vec<&str>> = HashMap::default();
        for (caller, callees) in &self.edges {
            for callee in callees {
                callers.entry(callee).or_default().push(caller);
            }
        }
        let mut pending: Vec<_> = bad.iter().cloned().collect();
        while let Some(callee) = pending.pop() {
            for caller in callers.get(callee.as_str()).into_iter().flatten() {
                if bad.insert((*caller).to_owned()) {
                    pending.push((*caller).to_owned());
                }
            }
        }
        let mut reached = roots.clone();
        let mut pending: Vec<_> = roots.iter().cloned().collect();
        while let Some(caller) = pending.pop() {
            for callee in self.edges.get(&caller).into_iter().flatten() {
                if reached.insert(callee.clone()) {
                    pending.push(callee.clone());
                }
            }
        }
        LoweringRegion::checked(
            reached
                .into_iter()
                .filter(|s| self.edges.contains_key(s) && !bad.contains(s)),
        )
    }
}

/// Primitive values do not require a user-defined argument or return conversion.
fn scalar(ty: &Type) -> bool {
    matches!(ty, Type::Int(_) | Type::Float(_) | Type::Bool | Type::Str)
}

/// Visit every value expression in a block, including nested control flow.
fn visit_block(block: &Block, visit: &mut impl FnMut(&Expr)) {
    for statement in &block.stmts {
        match statement {
            Stmt::Let {
                value: Some(value), ..
            }
            | Stmt::Expr(value)
            | Stmt::Return(Some(value), _) => visit_expr(value, visit),
            Stmt::Assign { target, value, .. } => {
                visit_expr(target, visit);
                visit_expr(value, visit);
            }
            Stmt::While { cond, body, .. } => {
                visit_expr(cond, visit);
                visit_block(body, visit);
            }
            Stmt::For { iter, body, .. } => {
                visit_expr(iter, visit);
                visit_block(body, visit);
            }
            Stmt::Let { value: None, .. }
            | Stmt::Return(None, _)
            | Stmt::Break(_)
            | Stmt::Continue(_) => {}
        }
    }
}

/// Include closure bodies and all value children using the shared HIR walker.
fn visit_expr(expr: &Expr, visit: &mut impl FnMut(&Expr)) {
    visit(expr);
    brass_hir::captures::walk_subexprs(expr, &mut |child| visit_expr(child, visit));
}

#[cfg(test)]
mod tests {
    use super::{HashMap, HashSet, RegionGraph};

    /// Build only syntax/name tables; certification must not run inference.
    fn graph(source: &str) -> RegionGraph {
        let ast = brass_parser::parse(source).unwrap();
        let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
            source: None,
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errors.is_empty());
        RegionGraph::new(&program, &HashSet::default(), None)
    }

    /// Function values and calls inside closures both create exclusion edges.
    #[test]
    fn references_inside_values_and_closures_close_the_region() {
        let graph = graph(
            "fun E() -> int32 { return 1 }\nfun closure() { return () -> E() }\nfun value() { return E }\nfun main() { closure()\n value() }\n",
        );
        assert!(graph.edges["closure"].contains("E"));
        assert!(graph.edges["value"].contains("E"));
        assert!(
            graph
                .closed_region(
                    HashSet::from_iter(["E".into()]),
                    &HashSet::from_iter(["main".into()])
                )
                .is_empty()
        );
    }

    /// Possible warning emission or reflective discovery forbids early draining.
    #[test]
    fn warnings_and_keyed_templates_preserve_demand_timing() {
        assert!(!graph("fun mixed(a, b) { let x = a!\n return b! }\n").can_drain());
        assert!(!graph("fun mixed(a) { let x = a!\n return error(1) }\n").can_drain());
        assert!(!graph("type T = {}\nfun T.f(self, x) -> infer! { return x }\n").can_drain());
        assert!(graph("fun plain(x) { return x }\n").can_drain());
    }

    /// Only omitted bodies may bypass the warning preflight; membership is not coverage.
    #[test]
    fn unselected_warning_body_does_not_block_completion() {
        let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
            source: None,
            is_prelude: false,
            path: vec!["main".into()],
            ast: brass_parser::parse("fun mixed(a, b) { let x = a!\n return b! }\n").unwrap(),
        }]);
        assert!(errors.is_empty());
        let mut selected = HashSet::default();
        assert!(RegionGraph::new(&program, &HashSet::default(), Some(&selected)).can_drain());
        selected.insert(program.functions["mixed"].decl.span);
        assert!(!RegionGraph::new(&program, &HashSet::default(), Some(&selected)).can_drain());
        assert!(
            RegionGraph::new(
                &program,
                &HashSet::from_iter(["mixed".into()]),
                Some(&selected)
            )
            .can_drain()
        );
    }

    /// A bad callee excludes callers even when the caller itself is clean.
    #[test]
    fn bad_dependencies_remove_transitive_callers_but_not_clean_siblings() {
        let graph = RegionGraph {
            edges: HashMap::from_iter([
                (
                    "main".into(),
                    HashSet::from_iter(["B".into(), "good".into()]),
                ),
                ("B".into(), HashSet::from_iter(["E".into()])),
                ("E".into(), HashSet::default()),
                ("good".into(), HashSet::default()),
                ("cold".into(), HashSet::default()),
            ]),
            opaque: HashSet::default(),
            can_drain: true,
        };
        let region = graph.closed_region(
            HashSet::from_iter(["E".into()]),
            &HashSet::from_iter(["main".into()]),
        );
        assert_eq!(region.len(), 1);
        assert!(region.contains("good"));
        for symbol in ["main", "B", "E", "cold"] {
            assert!(!region.contains(symbol));
        }
    }
}
