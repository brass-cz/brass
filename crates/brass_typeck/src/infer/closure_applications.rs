//! Parameter types of a monomorphic `let` closure binding, decided by all of
//! its direct applications at once.
//!
//! A closure value that is not let-polymorphic (see `closure_schemes`) has
//! one type, and an application commits an open parameter to the argument it
//! passes (see `Checker::apply_callable`). Committed at the first application
//! alone, a numeric parameter would make the verdict depend on the order of
//! the calls: `f(an_int32); f(an_int64)` would be rejected while the reverse
//! order widens the `int32`. The back end joins the arguments of every call
//! of a closure value (`brass_engine::mono`). So before such a binding's first
//! use, the rest of its block (or of the module's top-level code) is walked
//! by the light pass to collect the arguments of every direct application,
//! and a numeric parameter is fixed at their value join
//! ([`brass_typesys::join_values`]) up front -- the type the back end
//! instantiates the closure at, whatever the order of the calls.

use super::*;
use brass_typesys::{JoinOperand, NumericLiteral};

/// The light walk's record of one closure binding's direct applications
/// (see [`Checker::pin_closure_parameters`]): the marker variable the binding
/// is seen as during the walk and, per application, each argument's type
/// and the numeric literal it is written as.
#[derive(Clone)]
pub(super) struct ApplicationProbe {
    /// Identity of the binding during speculative inference.
    pub(super) marker: u32,
    /// Candidate signature used when walking a closure assigned to the binding.
    pub(super) parameters: Vec<Type>,
    /// Assignment literal currently receiving the candidate parameters.
    pub(super) assignment: Option<Span>,
    /// Argument evidence, including unresolved arguments deferred to another walk.
    pub(super) applications: Vec<Vec<(Type, Option<NumericLiteral>)>>,
}

impl Checker<'_> {
    /// Fix open, unquantified parameters of initialized closure bindings at
    /// the numeric join of their direct applications in the remaining block.
    pub(super) fn pin_closure_parameters(
        &mut self,
        bindings: &binding_joins::BlockBindings<'_>,
        position: usize,
        scopes: &ScopeStack,
    ) {
        let Some((stmt, rest)) = bindings.after(position) else {
            return;
        };
        let Stmt::Let {
            pat,
            value: Some(_),
            ..
        } = stmt
        else {
            return;
        };
        if rest.is_empty() {
            return;
        }
        let mut names = Vec::new();
        self.collect_const_bindings(pat, &mut names);
        for name in names {
            self.pin_binding_parameters(&name, bindings, position, scopes);
        }
    }

    fn pin_binding_parameters(
        &mut self,
        name: &str,
        bindings: &binding_joins::BlockBindings<'_>,
        position: usize,
        scopes: &ScopeStack,
    ) {
        let Some(bound) = scopes.last().and_then(|frame| frame.get(name)) else {
            return;
        };
        let resolved = self.resolve(bound);
        let Type::Fun(param_types, _) = brass_hir::peel_modes(&resolved) else {
            return;
        };
        let open: Vec<usize> = param_types
            .iter()
            .enumerate()
            .filter(
                |(_, ty)| matches!(ty, Type::Unknown(id) if !self.closure_schemes.contains_key(id)),
            )
            .map(|(index, _)| index)
            .collect();
        if open.is_empty() {
            return;
        }
        let (_, rest) = bindings.after(position).expect("initialized binding");
        let indexed = bindings.literal_calls(name, position).map(|calls| {
            calls
                .into_iter()
                .map(|args| {
                    args.iter()
                        .map(|arg| {
                            let ty = self.infer_expr_light(
                                &arg.expr,
                                scopes,
                                &mut LightProps::default(),
                            );
                            (ty, value_literal(&arg.expr))
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        });
        let mut provisional = param_types.clone();
        let mut visited = Vec::new();
        loop {
            if visited.contains(&provisional) {
                return;
            }
            visited.push(provisional.clone());
            let applications = match &indexed {
                Some(applications) => applications.clone(),
                None => self.direct_applications(name, rest, scopes, &provisional),
            };
            #[cfg(test)]
            {
                // The original collector runs only in the test checker and
                // cannot leave its speculative observations in the real one.
                let mut oracle = self.fork_probe();
                let expected = oracle.legacy_direct_applications(name, rest, scopes, &provisional);
                assert_probe_evidence(&applications, &expected);
            }
            let mut next = provisional.clone();
            let mut complete = vec![false; param_types.len()];
            for &index in &open {
                let arguments: Vec<JoinOperand> = applications
                    .iter()
                    .filter(|arguments| arguments.len() == param_types.len())
                    .map(|arguments| {
                        let (ty, literal) = &arguments[index];
                        JoinOperand {
                            ty: ty.clone(),
                            literal: *literal,
                        }
                    })
                    .collect();
                // Unresolved recursive arguments are deferred, whereas known
                // nonnumeric arguments prevent a numeric signature commitment.
                if arguments.len() < 2
                    || arguments.iter().any(|arg| {
                        brass_hir::is_fully_known(&arg.ty) && !is_numeric_argument(&arg.ty)
                    })
                {
                    next[index] = param_types[index].clone();
                    continue;
                }
                complete[index] = arguments.iter().all(|arg| is_numeric_argument(&arg.ty));
                let known: Vec<_> = arguments
                    .into_iter()
                    .filter(|arg| is_numeric_argument(&arg.ty))
                    .collect();
                next[index] = brass_typesys::join_values(self.program, &known)
                    .ok()
                    .flatten()
                    .unwrap_or_else(|| param_types[index].clone());
            }
            if next == provisional {
                for index in open {
                    if complete[index] && is_numeric_argument(&next[index]) {
                        let _ = self.solver.unify(&param_types[index], &next[index]);
                    }
                }
                break;
            }
            provisional = next;
        }
    }

    /// The arguments of every direct application `name(..)` of the binding
    /// `name` in `rest` (closure bodies included, a shadowing binding
    /// excluded), each with its light type and literal, typed by a light
    /// walk from the environment `scopes`. The walk's own solver effects are
    /// rolled back.
    fn direct_applications(
        &mut self,
        name: &str,
        rest: &[Stmt],
        scopes: &ScopeStack,
        parameters: &[Type],
    ) -> Vec<Vec<(Type, Option<NumericLiteral>)>> {
        // The light walk also saves closure bodies and other observations.
        // A private checker owns all of those writes; only argument evidence
        // leaves the probe, never a provisional channel or diagnostic.
        let mut probe = self.fork_probe();
        let applications = probe.collect_direct_applications(name, rest, scopes, parameters);
        self.next_unknown = self.next_unknown.max(probe.next_unknown);
        self.solver.seed_var_counter(self.next_unknown);
        applications
    }

    fn collect_direct_applications(
        &mut self,
        name: &str,
        rest: &[Stmt],
        scopes: &ScopeStack,
        parameters: &[Type],
    ) -> Vec<Vec<(Type, Option<NumericLiteral>)>> {
        let Type::Unknown(marker) = self.fresh_unknown() else {
            unreachable!("a fresh inference variable is an unknown");
        };
        let mut env = scopes.clone();
        let mut frame = HashMap::default();
        frame.insert(name.to_string(), Type::Unknown(marker));
        env.push(Scope::new(frame));
        let snapshot = self.solver.snapshot();
        let saved = self.application_probe.replace(ApplicationProbe {
            marker,
            parameters: parameters.to_vec(),
            assignment: None,
            applications: Vec::new(),
        });
        self.infer_returns_stmts(rest, &mut env, &mut Vec::new(), &mut LightProps::default());
        let probe = std::mem::replace(&mut self.application_probe, saved);
        self.solver.rollback(snapshot);
        probe.map(|probe| probe.applications).unwrap_or_default()
    }

    #[cfg(test)]
    fn legacy_direct_applications(
        &mut self,
        name: &str,
        rest: &[Stmt],
        scopes: &ScopeStack,
        parameters: &[Type],
    ) -> Vec<Vec<(Type, Option<NumericLiteral>)>> {
        let Type::Unknown(marker) = self.fresh_unknown() else {
            unreachable!("a fresh inference variable is an unknown");
        };
        let mut env = scopes.clone();
        let mut frame = HashMap::default();
        frame.insert(name.to_string(), Type::Unknown(marker));
        env.push(Scope::new(frame));
        let snapshot = self.solver.snapshot();
        let saved = self.application_probe.replace(ApplicationProbe {
            marker,
            parameters: parameters.to_vec(),
            assignment: None,
            applications: Vec::new(),
        });
        let block = Block {
            stmts: rest.to_vec(),
            span: rest[0].span(),
        };
        self.infer_returns_block(
            &block,
            &mut env,
            &mut Vec::new(),
            &mut LightProps::default(),
        );
        let probe = std::mem::replace(&mut self.application_probe, saved);
        self.solver.rollback(snapshot);
        probe.map(|probe| probe.applications).unwrap_or_default()
    }

    /// Walk an assignment, seeding an assigned closure with the provisional
    /// parameters only when its target is the binding under investigation.
    pub(super) fn probe_assignment(
        &mut self,
        target: &Expr,
        value: &Expr,
        env: &ScopeStack,
        props: &mut LightProps,
    ) {
        let assignment = match (target, value, self.application_probe.as_ref()) {
            (Expr::Ident(name, _), Expr::Closure(..), Some(probe))
                if self.lookup(env, name).is_some_and(
                    |ty| matches!(self.resolve(&ty), Type::Unknown(id) if id == probe.marker),
                ) =>
            {
                Some(value.span())
            }
            _ => None,
        };
        let saved = self
            .application_probe
            .as_mut()
            .map(|probe| std::mem::replace(&mut probe.assignment, assignment));
        self.infer_expr_light(value, env, props);
        if let (Some(probe), Some(saved)) = (self.application_probe.as_mut(), saved) {
            probe.assignment = saved;
        }
    }

    /// Record the light walk's application `callee(args)` when `callee` is
    /// the binding the active probe looks for (the marker it is bound to);
    /// `false` for any other call. The arguments are typed here.
    pub(super) fn probe_application(
        &mut self,
        callee: &Type,
        args: &[Arg],
        env: &ScopeStack,
        props: &mut LightProps,
    ) -> bool {
        let Some(marker) = self.application_probe.as_ref().map(|probe| probe.marker) else {
            return false;
        };
        if !matches!(self.resolve(callee), Type::Unknown(id) if id == marker) {
            return false;
        }
        let arguments: Vec<(Type, Option<NumericLiteral>)> = args
            .iter()
            .map(|arg| {
                let ty = self.infer_expr_light(&arg.expr, env, props);
                (self.resolve(&ty), value_literal(&arg.expr))
            })
            .collect();
        if let Some(probe) = self.application_probe.as_mut() {
            probe.applications.push(arguments);
        }
        true
    }
}

/// Whether an argument type takes part in a parameter's join: a fully known
/// number, `null`, or a nullable number -- the values whose join only widens.
fn is_numeric_argument(ty: &Type) -> bool {
    match ty {
        Type::Int(_) | Type::Float(_) => true,
        Type::Nullable(inner) => matches!(**inner, Type::Never | Type::Int(_) | Type::Float(_)),
        _ => false,
    }
}

#[cfg(test)]
fn assert_probe_evidence(
    actual: &[Vec<(Type, Option<NumericLiteral>)>],
    expected: &[Vec<(Type, Option<NumericLiteral>)>],
) {
    fn canonicalize(
        values: &[Vec<(Type, Option<NumericLiteral>)>],
    ) -> Vec<Vec<(Type, Option<NumericLiteral>)>> {
        let mut mapping = std::collections::BTreeMap::new();
        values
            .iter()
            .map(|args| {
                args.iter()
                    .map(|(ty, literal)| {
                        for id in brass_hir::type_vars(ty) {
                            let next = mapping.len() as u32;
                            mapping.entry(id).or_insert(Type::Unknown(next));
                        }
                        (brass_hir::substitute_vars(ty, &mapping), *literal)
                    })
                    .collect()
            })
            .collect()
    }
    assert_eq!(
        canonicalize(actual),
        canonicalize(expected),
        "indexed application evidence differs from the full collector"
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn indexed_and_fallback_queries_match_the_full_collector() {
        // Each check also runs the independent collector for every candidate
        // round. Alias, capture, shadowing and recursive inputs force fallback.
        for suffix in [
            "f(1); f(2147483648)",
            "f(2147483648); f(1)",
            "let alias = f; alias(1); alias(2147483648)",
            "let g = () -> f(1); f(2147483648); g()",
            "if true { let f = (x) -> x; f(1) }; f(2147483648)",
            "f = (x) -> { if x == 0 { return x }; return f(x - 1) }; f(1); f(2147483648)",
            "f(null); f(1); f(2147483648)",
            "f(1); f(1, 2); f(2147483648)",
            "f(1); f(true)",
        ] {
            let source = format!("fun main() {{ let f = (x) -> x; f = (x) -> x; {suffix} }}");
            let ast = brass_parser::parse(&source.replace(';', "\n")).expect("parse");
            let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
                source: None,
                is_prelude: false,
                path: vec!["main".into()],
                ast,
            }]);
            assert!(errors.is_empty());
            super::super::analyze(&program);
        }
    }

    #[test]
    fn application_probe_does_not_publish_saved_closures_or_literal_observations() {
        let ast =
            brass_parser::parse("fun main() { let g = (x) -> { return 1 }\nf(1)\nf(2147483648) }")
                .unwrap();
        let (program, _) = brass_hir::lower(&[brass_hir::LoadedModule {
            source: None,
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        let mut checker =
            Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
        let body = &program.functions.values().next().unwrap().decl.body;
        let params = vec![checker.fresh_unknown()];
        let ret = checker.fresh_unknown();
        let mut scope = HashMap::default();
        scope.insert("f".into(), Type::Fun(params.clone(), Box::new(ret)));
        let scopes = vec![Scope::new(scope)];
        let first = checker.next_unknown;
        let result = checker.direct_applications("f", &body.stmts, &scopes, &params);
        assert_eq!(result.len(), 2);
        assert!(checker.closure_bodies.is_empty());
        assert!(checker.closure_result_bodies.is_empty());
        assert!(checker.return_literals.is_empty());
        assert!(checker.typed.expressions.is_empty());
        assert!(checker.errors.is_empty());
        assert!(checker.next_unknown > first);
    }
}
