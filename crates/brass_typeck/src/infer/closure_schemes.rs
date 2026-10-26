//! Let-polymorphism for closure bindings, with a value restriction.
//!
//! A generalized closure binding (see `brass_hir::generalize`) gets a type
//! scheme: the inference variables of its function type that are NOT free in
//! the environment at the binding are quantified, and every use of the name
//! instantiates them with fresh variables. A variable tied to something in
//! scope -- a captured `names` array the closure pushes into -- stays
//! monomorphic, so the first application commits it in the solver and a
//! later conflicting use is reported. Every other closure value is
//! monomorphic outright: its applications unify in the real solver (a `let`
//! binding's numeric parameter is first fixed at the join of its direct
//! applications, see `closure_applications`).
//!
//! A scheme is recorded per quantified variable rather than per binding:
//! the quantified variables occur only in the binding's own type (and in its
//! body's records, which nothing unifies with after generalization), so a
//! type that mentions one of them -- wherever a scope lookup finds it -- is
//! an occurrence of the generalized binding. That covers locals, captured
//! scopes and module globals alike without a second binding table.
//!
//! A closure returned from a concrete instance has its open parameters fixed
//! from its body's use when the instance's check ends, since it is compiled
//! with that instance (see [`Checker::settle_escaping_closures`]).

use std::collections::BTreeMap;

use super::*;

impl Checker<'_> {
    /// Generalize the closure value `ty` just bound by a `let`/`const` at the
    /// binding span `span`, when the binding is generalizable: quantify the
    /// variables of its type not free in `scopes` (the environment at the
    /// binding, before the name itself is bound).
    pub(super) fn generalize_closure_binding(
        &mut self,
        span: Span,
        ty: &Type,
        scopes: &ScopeStack,
    ) {
        if !self.generalizable.contains(&span) {
            return;
        }
        let resolved = self.resolve(ty);
        if !matches!(peel_modes(&resolved), Type::Fun(..)) {
            return;
        }
        let env_free = self.environment_free_vars(scopes);
        self.quantify_closure_vars(&resolved, &env_free);
    }

    /// Record the variables of `ty` outside `env_free` as one closure scheme.
    fn quantify_closure_vars(&mut self, ty: &Type, env_free: &HashSet<u32>) {
        let mut vars: Vec<u32> = self
            .solver
            .free_vars(ty)
            .into_iter()
            .filter(|v| !env_free.contains(v))
            .collect();
        if vars.is_empty() {
            return;
        }
        vars.sort_unstable();
        let scheme: Rc<[u32]> = vars.into();
        for v in scheme.iter() {
            self.closure_schemes.insert(*v, Rc::clone(&scheme));
        }
    }

    /// The inference variables free in the environment `scopes`: every
    /// binding's type (a narrowing only refines a binding's own type) and
    /// every enclosing callable's declared return context. A closure variable
    /// shared with any of them is not generalized (the value restriction).
    pub(super) fn environment_free_vars(&self, scopes: &ScopeStack) -> HashSet<u32> {
        let mut out = HashSet::default();
        for frame in scopes {
            for ty in frame.values() {
                out.extend(self.solver.free_vars(ty));
            }
        }
        for context in &self.return_contexts {
            if let ReturnContext::Explicit(ty) = context {
                out.extend(self.solver.free_vars(ty));
            }
        }
        out
    }

    /// The type a use of a binding of type `ty` sees: a generalized closure's
    /// scheme instantiated with fresh variables (of the same kinds, carrying
    /// the same deferred shape constraints and the same saved body, so the
    /// application re-checks it at its own argument types); any other type
    /// unchanged.
    pub(super) fn instantiate_closure_scheme(&mut self, ty: Type) -> Type {
        self.instantiate_scheme(ty, true)
    }

    /// [`Self::instantiate_closure_scheme`] for the light walk, whose
    /// instances are approximations and make no display observation.
    pub(super) fn instantiate_closure_scheme_light(&mut self, ty: Type) -> Type {
        self.instantiate_scheme(ty, false)
    }

    fn instantiate_scheme(&mut self, ty: Type, observe: bool) -> Type {
        if self.closure_schemes.is_empty() {
            return ty;
        }
        let resolved = self.resolve(&ty);
        let mut mapping: BTreeMap<u32, Type> = BTreeMap::new();
        for var in brass_hir::type_vars(&resolved) {
            let Some(scheme) = self.closure_schemes.get(&var).cloned() else {
                continue;
            };
            for &v in scheme.iter() {
                if mapping.contains_key(&v) {
                    continue;
                }
                let fresh = self.fresh_unknown();
                let Type::Unknown(id) = fresh else {
                    unreachable!("fresh_unknown is a variable");
                };
                if let Some(kind) = self.solver.kind_of(v) {
                    self.solver.record_var(id, kind);
                }
                if observe {
                    self.closure_instantiations.push((v, id));
                }
                mapping.insert(v, fresh);
            }
        }
        if mapping.is_empty() {
            return ty;
        }
        // The deferred shape constraints carry over to the instance, over
        // the instance's own variables.
        for (v, fresh) in &mapping {
            let Type::Unknown(id) = fresh else { continue };
            if let Some(body) = self.closure_result_bodies.get(v).cloned() {
                self.closure_result_bodies.insert(*id, body);
            }
            if let Some(shapes) = self.shape_constraints.get(v).cloned() {
                let shapes = shapes.iter().map(|c| c.substitute(&mapping)).collect();
                self.shape_constraints.insert(*id, shapes);
            }
        }
        let instance = brass_hir::substitute_vars(&resolved, &mapping);
        // The application of an instance re-checks the closure's body at the
        // instance's argument types: share the saved body under the
        // instantiated parameters.
        if let (Type::Fun(params, _), Type::Fun(inst_params, _)) =
            (peel_modes(&resolved), peel_modes(&instance))
            && let Some(body) = self.closure_bodies.get(params).cloned()
        {
            self.closure_bodies.insert(inst_params.clone(), body);
        }
        instance
    }

    /// Turn the instantiations made so far into display-only observations of
    /// the generalized closures' own variables (`closure_bindings`): a scheme
    /// variable every use instantiated to one type shows that type, one used
    /// at several types stays open.
    pub(super) fn settle_closure_instantiations(&mut self) {
        for (var, fresh) in std::mem::take(&mut self.closure_instantiations) {
            let observed = self.resolve(&Type::Unknown(fresh));
            if brass_hir::is_fully_known(&observed) {
                self.record_closure_binding(var, &observed);
            }
        }
    }

    /// Fix the still-open parameter types of the closures a concrete
    /// instance returns, from how each closure's body uses them: a closure
    /// that escapes its defining body is compiled with that body's instance,
    /// so its parameters must be known by the end of that body's check. A
    /// parameter compared or combined with a known type takes it -- `(x) -> x
    /// + n` with `n: int32` takes `int32`, next to a literal the literal's
    /// default. One with no such use stays open (its first application fixes
    /// it, as for any monomorphic closure) and is remembered: if nothing ever
    /// fixes it, `report_undetermined_closures` asks for an annotation.
    pub(super) fn settle_escaping_closures(&mut self, ret: &Type) {
        let resolved = self.resolve(ret);
        let mut funs = Vec::new();
        collect_function_types(&resolved, &mut funs);
        for params in funs {
            let literal = self
                .closure_bodies
                .get(&params)
                .and_then(|body| match &body.expr {
                    Expr::Closure(_, _, span) => Some(*span),
                    _ => None,
                });
            let mut open = false;
            for param in &params {
                let Type::Unknown(id) = self.resolve_head(param) else {
                    continue;
                };
                let default = self.shape_constraints.get(&id).and_then(|shapes| {
                    shapes.iter().find_map(|shape| match shape {
                        ShapeConstraint::Equals(t) => Some(t.clone()),
                        ShapeConstraint::Operand { other, .. } => Some(other.clone()),
                        _ => None,
                    })
                });
                match default {
                    Some(t) => {
                        if let Some(span) = literal {
                            self.verify_shape_constraints(param, &t, span);
                        }
                        let _ = self.solver.unify(param, &t);
                    }
                    None => open = true,
                }
            }
            if open && let Some(span) = literal {
                self.undetermined_closures.push(span);
            }
        }
    }

    /// Report each closure remembered by `settle_escaping_closures` whose
    /// parameter types nothing in the program ever fixed: the back ends
    /// compile a closure value at its parameter types, so an escaping one
    /// needs an annotation then. Run once all bodies are checked.
    pub(super) fn report_undetermined_closures(&mut self) {
        if self.undetermined_closures.is_empty() {
            return;
        }
        let known: HashSet<Span> = self
            .typed
            .expressions
            .iter()
            .filter(|e| matches!(e.kind, brass_hir::TypedExprKind::Closure))
            .filter(|e| brass_hir::is_fully_known(&self.solver.resolve(&e.ty)))
            .map(|e| e.span)
            .collect();
        let mut spans = std::mem::take(&mut self.undetermined_closures);
        spans.sort_by_key(|s| (s.lo, s.hi));
        spans.dedup();
        for span in spans {
            if !known.contains(&span) {
                self.errors.push(TypeError {
                    message: "cannot infer the parameter types of a closure that escapes the \
                              function creating it: annotate its parameters"
                        .to_string(),
                    span,
                });
            }
        }
    }
}

/// The parameter lists of the function types in `ty`: its own, those of the
/// functions a function type returns, and those inside its elements, fields
/// and payloads.
fn collect_function_types(ty: &Type, out: &mut Vec<Vec<Type>>) {
    match ty {
        Type::Fun(params, ret) => {
            out.push(params.clone());
            collect_function_types(ret, out);
        }
        Type::Array(inner, _)
        | Type::Slice(inner)
        | Type::Nullable(inner)
        | Type::ConstOf(inner)
        | Type::Mut(inner)
        | Type::Ref(inner) => collect_function_types(inner, out),
        Type::Tuple(elems) => elems.iter().for_each(|e| collect_function_types(e, out)),
        Type::Record(n) | Type::Sum(n) => n
            .substitution
            .iter()
            .for_each(|(_, t)| collect_function_types(t, out)),
        _ => {}
    }
}
