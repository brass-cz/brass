//! Closure body checking at definition and concrete application types.

use super::*;

impl Checker<'_> {
    /// Retain open closure bodies because their patterns and other operations
    /// can require concrete argument types before they can be validated.
    pub(super) fn remember_closure(
        &mut self,
        expr: &Expr,
        params: &[Type],
        scopes: &ScopeStack,
        explicit_return: bool,
        result_identity: Option<u32>,
    ) {
        let resolved: Vec<_> = params.iter().map(|ty| self.resolve(ty)).collect();
        let open_params = !resolved.iter().all(brass_hir::is_fully_known);
        if !open_params && result_identity.is_none() {
            return;
        }
        self.observe_method_closure();
        if let Some(frame) = self.elaboration_journals.last_mut() {
            frame.has_closure_bodies = true;
        }
        let body = Rc::new(ClosureBody {
            expr: expr.clone(),
            numeric_replay: closure_memo::closed_numeric_body(expr),
            explicit_return,
            scopes: scopes.clone(),
            narrowing_facts: Rc::clone(&self.narrowing_facts),
            const_scopes: self.const_scopes.clone(),
            module: self.current_module.clone(),
            self_type: self.self_type.clone(),
            self_variant: self.self_variant.clone(),
        });
        // Body inference may constrain a parameter to a container with open
        // elements. Both the original variable and its resolved shape can
        // reach a later application through value lookup.
        if let Some(id) = result_identity {
            self.closure_result_bodies.insert(id, Rc::clone(&body));
        }
        if open_params {
            self.closure_bodies
                .insert(params.to_vec(), Rc::clone(&body));
            self.closure_bodies.insert(resolved, body);
        }
    }

    /// Recover a closure by its result identity or its open parameters.
    /// Result identities distinguish captured-result and zero-argument closures.
    pub(super) fn saved_closure_body(
        &self,
        params: &[Type],
        ret: &Type,
    ) -> Option<Rc<ClosureBody>> {
        let by_result = match ret {
            Type::Unknown(id) => self.closure_result_bodies.get(id),
            _ => None,
        };
        by_result
            .or_else(|| self.closure_bodies.get(params))
            .cloned()
    }

    /// Check a closure's body in its lexical environment at the (now
    /// concrete) parameter types of one application, so the body's
    /// concrete-type errors are reported. The check is rolled back: the
    /// application's own unifications already fixed what the closure's type
    /// records. Source diagnostics retain the offending body's original spans.
    ///
    /// Returns what the body returns at these argument types when that is
    /// fully known -- the application's result, which the closure's own
    /// return type may not have expressed while its parameters were open:
    /// `(q) -> q.b` applied to a record returns that record's field type. A
    /// still-open return of the closure is committed to it, so the closure
    /// value's type is complete once its parameters are.
    pub(super) fn check_callable_body(&mut self, params: &[Type], ret: &Type) -> Option<Type> {
        let closure = self.saved_closure_body(params, ret)?;
        let concrete: Vec<_> = params.iter().map(|ty| self.resolve(ty)).collect();
        if !concrete.iter().all(brass_hir::is_fully_known) {
            return None;
        }
        let Expr::Closure(decl_params, body, span) = &closure.expr else {
            unreachable!("only closures have saved callable bodies");
        };
        let key = format!("closure:{}", span.lo);
        if !self.instantiating.insert(key.clone()) {
            return None;
        }
        let memo_key = self.closure_memo_key(&closure, &concrete, ret);
        if let Some(entry) = memo_key
            .as_ref()
            .and_then(|key| self.closure_memo.get(key))
            .cloned()
        {
            #[cfg(test)]
            {
                self.closure_memo_hits += 1;
            }
            let observed = Some(self.replay_numeric_closure(&entry));
            self.last_closure_result = None;
            self.instantiating.remove(&key);
            return self.finish_callable_result(closure.explicit_return, ret, observed);
        }
        let saved_module = std::mem::replace(&mut self.current_module, closure.module.clone());
        let saved_self = std::mem::replace(&mut self.self_type, closure.self_type.clone());
        let saved_variant = std::mem::replace(&mut self.self_variant, closure.self_variant.clone());
        let saved_consts = std::mem::replace(&mut self.const_scopes, closure.const_scopes.clone());
        // The body is checked in the environment of its literal, whose
        // narrowings were already restricted to the ones a closure may trust.
        let saved_facts = std::mem::replace(
            &mut self.narrowing_facts,
            Rc::clone(&closure.narrowing_facts),
        );
        // The globals' own variables (the bottom frame of every body's
        // scopes). Running the closure at these argument types may pin them --
        // a call that pushes into a global list fixes its element type -- and
        // that is a real effect of the program, not part of the speculation.
        let global_vars: Vec<u32> = closure
            .scopes
            .first()
            .map(|globals| {
                let mut vars: Vec<u32> = globals
                    .values()
                    .flat_map(brass_hir::type_vars)
                    .filter(|id| *id != brass_hir::INFER_VAR)
                    .collect();
                vars.sort_unstable();
                vars.dedup();
                vars
            })
            .unwrap_or_default();
        let snapshot = self.solver.snapshot();
        let diagnostics = (self.errors.len(), self.warnings.len());
        if memo_key.is_some() {
            self.begin_elaboration_journal();
        }
        self.speculation_depth += 1;
        self.check_closure_against(
            &closure.expr,
            decl_params,
            body,
            (
                &concrete,
                closure.explicit_return.then(|| self.resolve(ret)).as_ref(),
            ),
            &mut closure.scopes.clone(),
        );
        if self.numeric.probing {
            self.numeric.result = self.numeric.closure_result.clone();
        }
        let observed = self
            .last_closure_result
            .take()
            .map(|ty| self.resolve(&ty))
            .filter(brass_hir::is_fully_known);
        self.speculation_depth -= 1;
        let memo_entry = if memo_key.is_some() {
            let frame = self.finish_elaboration_journal();
            if diagnostics == (self.errors.len(), self.warnings.len()) {
                observed
                    .as_ref()
                    .and_then(|ty| self.build_numeric_closure_memo(ty, frame))
            } else {
                None
            }
        } else {
            None
        };
        let effects: Vec<(Type, Type)> = global_vars
            .into_iter()
            .map(|id| (Type::Unknown(id), self.resolve(&Type::Unknown(id))))
            .filter(|(var, pinned)| var != pinned)
            .collect();
        self.solver.rollback(snapshot);
        // Keep what the application did to global state; the bindings of the
        // closure's own variables are undone, so it stays polymorphic in
        // everything that does not reach a global.
        for (var, pinned) in effects {
            let snapshot = self.solver.snapshot();
            if self.solver.unify(&var, &pinned).is_err() {
                self.solver.rollback(snapshot);
            }
        }
        self.narrowing_facts = saved_facts;
        self.const_scopes = saved_consts;
        self.self_type = saved_self;
        self.self_variant = saved_variant;
        self.current_module = saved_module;
        self.instantiating.remove(&key);
        let result = self.finish_callable_result(closure.explicit_return, ret, observed);
        if let (Some(key), Some(entry)) = (memo_key, memo_entry) {
            self.closure_memo.insert(key, Rc::new(entry));
        }
        result
    }

    fn finish_callable_result(
        &mut self,
        explicit_return: bool,
        ret: &Type,
        observed: Option<Type>,
    ) -> Option<Type> {
        if let Some(observed) = &observed
            && !brass_hir::is_fully_known(&self.resolve(ret))
        {
            let _ = self.solver.unify(ret, observed);
        }
        if explicit_return {
            Some(self.resolve(ret))
        } else {
            observed
        }
    }

    /// Check a closure at the given parameter types. An explicit return
    /// controls body literals and conversions; otherwise infer the result
    /// from this concrete body's returns.
    pub(super) fn check_closure_against(
        &mut self,
        expr: &Expr,
        params: &[Param],
        body: &Expr,
        (want_params, expected_ret): (&[Type], Option<&Type>),
        scopes: &mut ScopeStack,
    ) -> Type {
        let inferred_ret = self.fresh_unknown();
        let want_ret = expected_ret.unwrap_or(&inferred_ret);
        self.report_duplicate_params("closure", params);
        let mut closure_scope: HashMap<String, Type> = HashMap::default();
        let mut param_types = Vec::with_capacity(params.len());
        for (i, p) in params.iter().enumerate() {
            let expected = want_params
                .get(i)
                .cloned()
                .unwrap_or_else(|| self.fresh_unknown());
            // An explicit parameter annotation still applies; the complete
            // function type is checked after the body so parameter variance and
            // passing mode are decided together. An unannotated parameter takes
            // the expected type directly.
            let ty = match &p.ty {
                Some(te) => self
                    .resolve_type(te)
                    .unwrap_or_else(|_| self.fresh_unknown()),
                None => expected,
            };
            if p.name != "_" {
                closure_scope.insert(p.name.clone(), ty.clone());
            }
            param_types.push(ty);
        }
        let mut closure_scopes = scopes.clone();
        closure_scopes.push(Scope::new(closure_scope));
        let mut light_props = LightProps::default();
        self.infer_expr_light(body, &closure_scopes, &mut light_props);
        // A FALLIBLE closure body checked against a still-open expected
        // return: bind the expectation to `Result<ok, err>` up front, so the
        // body's returns reconcile order-independently -- a bare `return v`
        // against the Ok payload, a `return error(..)` against the whole
        // Result (the shape a named callable's `T!` annotation resolves to).
        // Left open, the first return seen would fix the shape and the other
        // kind would clash against it.
        if matches!(self.resolve(want_ret), Type::Unknown(_)) && !light_props.errors.is_empty() {
            let ok = self.fresh_unknown();
            let err = self
                .reconcile_error_payloads(&light_props.errors, true)
                .unwrap_or_else(|| self.fresh_unknown());
            let span = light_props
                .errors
                .first()
                .map(|(_, s)| *s)
                .unwrap_or(brass_parser::Span::new(0, 0));
            let inferred = self.scoped_result(ok, err, span);
            let _ = self.solver.unify(want_ret, &inferred);
        }
        self.const_scopes.push(HashSet::default());
        if self.numeric_enabled {
            self.enter_closure_instance(params, body, &param_types, scopes);
        }
        if self.numeric.probing {
            self.enter_numeric_body(body.span());
            self.numeric.returns.push(Vec::new());
        }
        self.return_contexts.push(match expected_ret {
            Some(ret) => ReturnContext::Explicit(ret.clone()),
            None => ReturnContext::Inferred,
        });
        self.return_values.push(Vec::new());
        // An expression body that is an anonymous record literal for a
        // declared record result is built as that record (and checked there),
        // and a bracket literal with an explicit tuple result retains that
        // contract when its concrete element types could also form an array.
        let literal_result = (!matches!(body, Expr::Block(..)))
            .then(|| self.expression_body_result(want_ret))
            .filter(|want| {
                self.is_anonymous_literal_into(body, want)
                    || (matches!(body, Expr::Array(..))
                        && matches!(self.resolve(want), Type::Tuple(_)))
            });
        // The body runs when the closure is called, not here: it is not part
        // of the enclosing path's narrowing flow.
        let body_val = self.with_detached_flow(|this| match (&literal_result, body) {
            (Some(want), _) => this.check_expr_against(body, want, &mut closure_scopes),
            (None, Expr::Block(block, _)) => {
                this.check_closure_block_body(body, block, &mut closure_scopes)
            }
            (None, _) => this.check_expr(body, &mut closure_scopes),
        });
        let returned = self.return_values.pop().unwrap_or_default();
        if self.numeric.probing {
            let origins = self.numeric.returns.pop().unwrap_or_default();
            self.leave_numeric_body(true);
            self.numeric.closure_result = if expected_ret.is_some() {
                None
            } else if matches!(body, Expr::Block(..)) {
                if !origins.is_empty() && origins.iter().all(|source| *source == origins[0]) {
                    origins[0].clone()
                } else {
                    None
                }
            } else {
                self.numeric_source(body)
            };
        }
        if self.numeric_enabled {
            self.leave_instance();
        }
        self.return_contexts.pop();
        self.const_scopes.pop();
        // What this check of the body returns (see `last_closure_result`),
        // with its propagation layers.
        self.last_closure_result =
            Some(self.closure_body_result(body, body_val.clone(), returned, light_props.clone()));
        // An expression-bodied closure (not a `{ ... }` block) returns its body
        // value directly, so that value must match the expected return; a block
        // body returns through the `return` context handled above. Against a
        // RESULT expectation (a fallible closure -- the pre-binding above, or
        // an explicitly Result-typed parameter) a bare body value is the Ok
        // payload, exactly as `check_return` treats a bare `return v`; a body
        // that is itself a whole Result (an `error(..)`, a forwarded fallible
        // call) flows whole.
        if expected_ret.is_some() && !matches!(body, Expr::Block(..)) && literal_result.is_none() {
            let resolved_want = self.resolve(want_ret);
            let want_result = match &resolved_want {
                Type::Nullable(inner) if inner.is_result_type() => Some(inner.as_ref()),
                other if other.is_result_type() => Some(other),
                _ => None,
            };
            match want_result.and_then(|w| w.result_payloads()) {
                Some((ok, _err)) if !self.resolve(&body_val).is_result_type() => {
                    let ok = ok.clone();
                    self.expect_expr_assignable(&body_val, &ok, body);
                }
                _ => {
                    self.expect_expr_assignable(&body_val, want_ret, body);
                }
            }
        }
        let result = expected_ret.cloned().unwrap_or_else(|| {
            self.last_closure_result
                .clone()
                .expect("checked closure result")
        });
        self.remember_closure(expr, &param_types, scopes, expected_ret.is_some(), None);
        let ty = Type::Fun(param_types, Box::new(result));
        self.record_expr_type(expr, &ty);
        ty
    }

    /// Record inferred brackets without exporting a provisional tuple shape.
    /// Concrete closure elaboration supplies the creation instance's result;
    /// resolving its original element variables alone cannot settle the shape.
    pub(super) fn record_inferred_expr_type(&mut self, expr: &Expr, ty: &Type) {
        if matches!(expr, Expr::Array(..)) && has_provisional_tuple(&self.resolve(ty)) {
            self.record_expr_type(expr, &Type::Unknown(brass_hir::INFER_VAR));
        } else {
            self.record_expr_type(expr, ty);
        }
    }

    /// Keep a bracket-dependent inferred result open until the saved body
    /// is checked at concrete arguments. Independent tuple element variables
    /// are provisional evidence, not an explicit tuple contract.
    pub(super) fn inferred_closure_result(&mut self, ret: Type) -> (Type, Option<u32>) {
        if has_provisional_tuple(&self.resolve(&ret)) {
            let result = self.fresh_unknown();
            let Type::Unknown(id) = result else {
                unreachable!("fresh inference results are variables");
            };
            (result, Some(id))
        } else {
            (ret, None)
        }
    }
}

fn has_provisional_tuple(ty: &Type) -> bool {
    match ty {
        Type::Tuple(_) => !brass_hir::is_fully_known(ty),
        Type::Slice(inner)
        | Type::Array(inner, _)
        | Type::Nullable(inner)
        | Type::ConstOf(inner)
        | Type::Mut(inner)
        | Type::Ref(inner) => has_provisional_tuple(inner),
        Type::Record(n) | Type::Sum(n) => n
            .substitution
            .iter()
            .any(|(_, ty)| has_provisional_tuple(ty)),
        _ => false,
    }
}
