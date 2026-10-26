//! The light walk: a cheap, best-effort typing of a body that reports no
//! errors and collects the values the body returns and its propagation sites
//! ([`LightProps`]). The pre-pass runs it to discover unannotated returns
//! and the provisional global types (see `precompute`); a call-site
//! elaboration runs it again on the body the full check just walked, at the
//! instance's types and following the full check's static folds (see
//! `Checker::light_folds`); and it collects a monomorphic closure binding's
//! applications (see `closure_applications`).

use super::*;

impl<'a> Checker<'a> {
    /// Walk `block` in the light environment `env`, collecting each returned
    /// value's type and span into `normal` and the body's propagation sites
    /// into `props`.
    pub(super) fn infer_returns_block(
        &mut self,
        block: &Block,
        env: &mut ScopeStack,
        normal: &mut Vec<(Type, Span)>,
        props: &mut LightProps,
    ) {
        self.infer_returns_stmts(&block.stmts, env, normal, props);
    }

    /// Walk a borrowed statement sequence with the same scope and return
    /// handling as a block, without copying its expressions.
    pub(super) fn infer_returns_stmts(
        &mut self,
        stmts: &[Stmt],
        env: &mut ScopeStack,
        normal: &mut Vec<(Type, Span)>,
        props: &mut LightProps,
    ) {
        for stmt in stmts {
            match stmt {
                Stmt::Let {
                    pat,
                    ty,
                    value,
                    is_const,
                    ..
                } => {
                    let ty =
                        self.light_let_type(ty.as_ref(), value.as_ref(), *is_const, env, props);
                    self.bind_pattern_light(pat, &ty, env);
                }
                Stmt::Assign { target, value, .. } => {
                    self.probe_assignment(target, value, env, props);
                }
                Stmt::Expr(value) => {
                    // Grow a locally-built collection's element type: a
                    // `result = []` then `result.push(x)` pins `result`'s element
                    // to `x`, so an unannotated function that returns the built
                    // collection (e.g. `slice`/`map`) infers its element type from
                    // the values pushed -- which the rest of this light pass would
                    // otherwise miss, leaving the return an unconstrained `?[]`.
                    self.track_collection_growth(value, env, props);
                    self.infer_returns_expr(value, env, normal, props);
                }
                Stmt::While { cond, body, .. } => {
                    self.infer_expr_light(cond, env, props);
                    self.infer_returns_block(body, &mut env.clone(), normal, props);
                }
                Stmt::For {
                    pat, iter, body, ..
                } => {
                    let iter_ty = self.infer_expr_light(iter, env, props);
                    let item_ty =
                        brass_hir::index_element(&iter_ty).unwrap_or_else(|| self.fresh_unknown());
                    let mut inner = env.clone();
                    self.bind_pattern_light(pat, &item_ty, &mut inner);
                    self.infer_returns_block(body, &mut inner, normal, props);
                }
                Stmt::Return(Some(expr), _) => {
                    let ty = self.infer_expr_light(expr, env, props);
                    let resolved = self.resolve(&ty);
                    match resolved.result_payloads() {
                        Some((ok, err)) if ok.is_unknown() => {
                            // A forwarded error is re-raised lifted into the
                            // prelude `Error` (see the full check's
                            // `link_forwarded_error`).
                            let lifted = crate::lift_err_payload(self.program, self.resolve(err));
                            props.errors.push((lifted, expr.span()))
                        }
                        _ => {
                            self.note_return_literal(expr.span(), expr);
                            normal.push((ty, expr.span()))
                        }
                    }
                }
                Stmt::Return(None, span) => normal.push((Type::Void, *span)),
                Stmt::Break(_) | Stmt::Continue(_) => {}
            }
            // A statically decided chain whose selected arm always returns
            // kills the fall-through for this instance; the remaining
            // statements' returns belong to nothing this instance compiles.
            if self.light_chain_diverges(stmt, env, props) {
                break;
            }
        }
    }

    /// Decide a type-test `if` condition against the light environment:
    /// `Some(matched)` when `cond` is a type test whose subject's type is
    /// already fully known (a per-instance pass), `None` otherwise -- either
    /// not a type test at all, or the definitional pass, where nothing is
    /// selected and both arms stay walked. The pattern is the channel entry
    /// the full check just recorded (holes pinned by the tested arm); a
    /// missing entry falls back to the syntactic annotation with every hole a
    /// wildcard.
    fn light_type_test_decision(
        &mut self,
        cond: &Expr,
        env: &ScopeStack,
        props: &mut LightProps,
    ) -> Option<bool> {
        let Expr::TypeTest(subject, te, negated, tspan) = cond else {
            return None;
        };
        let subject_ty = self.infer_expr_light(subject, env, props);
        let subject_ty = self.resolve(&subject_ty);
        if !brass_hir::is_fully_known(&subject_ty) {
            return None;
        }
        let pattern = match self.type_tests.get(tspan) {
            Some(p) => p.clone(),
            None => {
                let resolved = self.resolve_type(te).ok()?;
                let resolved = self.resolve(&resolved);
                super::expr::wildcard_open_vars(&resolved)
            }
        };
        Some(brass_typesys::type_test_accepts(self.program, &pattern, &subject_ty) != *negated)
    }

    /// Decide the condition of the `if` at `span` against the light
    /// environment, as the full check folds it: the decision the full check
    /// of this elaboration recorded (see `Checker::light_folds`); otherwise a
    /// type test (see [`Self::light_type_test_decision`]) or a
    /// member-presence test whose member's type alone decides it (an absent
    /// member is always false, a present non-nullable one always true).
    /// `None` leaves both arms walked. A condition that is a binding whose
    /// type the walk left open marks `props.open_static_test`: its instances
    /// may each fold it their own way.
    fn light_condition_decision(
        &mut self,
        span: Span,
        cond: &Expr,
        env: &ScopeStack,
        props: &mut LightProps,
    ) -> Option<bool> {
        if let Some(decided) = self.light_folds.get(&span) {
            return Some(*decided);
        }
        if let Some(decided) = self.light_type_test_decision(cond, env, props) {
            return Some(decided);
        }
        if let Expr::Ident(name, _) = cond
            && let Some(ty) = self.lookup(env, name)
            && !brass_hir::is_fully_known(&self.resolve(&ty))
        {
            props.open_static_test = true;
            return None;
        }
        self.light_member_test_type(cond, env, props)?
            .static_truthiness()
    }

    /// Decide the `if let <binding> = scrut` at `span`: the full check's
    /// recorded decision, else -- when `scrut` is a member access -- the
    /// presence test's truth (false for an absent member, the always-null
    /// `never?`; true for a present non-nullable one, which binds
    /// irrefutably). `None` leaves both arms walked.
    fn light_presence_binding_decision(
        &mut self,
        span: Span,
        pat: &Pattern,
        scrut: &Expr,
        env: &ScopeStack,
        props: &mut LightProps,
    ) -> Option<bool> {
        if let Some(decided) = self.light_folds.get(&span) {
            return Some(*decided);
        }
        if !matches!(pat, Pattern::Binding(_, None, _)) {
            return None;
        }
        presence_binding_truth(&self.light_member_test_type(scrut, env, props)?)
    }

    /// The type of the uncalled member access `expr` (`base.name`) when this
    /// walk knows it as the full check would: the base's type is fully known
    /// and names the member's type -- a present method decays to its name (a
    /// `string`), an absent member is the always-null `never?`. `None` for
    /// any other expression, or when the type is not known here. A base that
    /// is a binding whose type is still open (an unannotated parameter in the
    /// definitional walk) marks `props.open_static_test`: its instances
    /// decide the test, each its own way.
    fn light_member_test_type(
        &mut self,
        expr: &Expr,
        env: &ScopeStack,
        props: &mut LightProps,
    ) -> Option<Type> {
        let Expr::Field(base, name, _) = expr else {
            return None;
        };
        let bound = match &**base {
            Expr::Ident(n, _) => self.lookup(env, n).is_some(),
            Expr::SelfExpr(_) => true,
            _ => false,
        };
        if self.unit_variant_type(base, name, bound).is_some() {
            return None;
        }
        let base_ty = self.infer_expr_light(base, env, props);
        let resolved = self.resolve(&base_ty);
        let peeled = brass_hir::peel_modes(&resolved).clone();
        if !brass_hir::is_fully_known(&peeled) {
            props.open_static_test |= bound;
            return None;
        }
        if let Some(present) = self.program.member_presence(&peeled, name) {
            return Some(if present { Type::Str } else { Type::null() });
        }
        let Type::Record(record) = &peeled else {
            return None;
        };
        let ty = match record.substitution.get(name) {
            Some(ty) => ty.clone(),
            None => {
                let info = self.program.type_by_id(record.id)?;
                let TypeKind::Record { fields, .. } = &info.kind else {
                    return None;
                };
                match fields.iter().find(|f| f.name == *name) {
                    Some(field) => {
                        brass_hir::substitute_self(field.resolved_ty.as_ref()?, &info.type_ref())
                    }
                    None => Type::null(),
                }
            }
        };
        let ty = self.resolve(&ty);
        brass_hir::is_fully_known(&ty).then_some(ty)
    }

    /// Whether `stmt` holds a statically decided `if`/`if let` chain (see
    /// [`Self::light_condition_decision`]) whose selected arm always returns
    /// for this instance: the light walk then stops collecting the
    /// enclosing block's remaining statements, which the back end never
    /// compiles for this instance (`check_block` isolates them the same way).
    fn light_chain_diverges(
        &mut self,
        stmt: &Stmt,
        env: &ScopeStack,
        props: &mut LightProps,
    ) -> bool {
        let expr = match stmt {
            Stmt::Expr(e) => e,
            Stmt::Let {
                value: Some(value), ..
            } => value,
            _ => return false,
        };
        self.light_if_chain_diverges(expr, env, props)
    }

    fn light_if_chain_diverges(
        &mut self,
        expr: &Expr,
        env: &ScopeStack,
        props: &mut LightProps,
    ) -> bool {
        let (decision, then, els) = match expr {
            Expr::If(cond, then, els, span) => (
                self.light_condition_decision(*span, cond, env, props),
                then,
                els,
            ),
            Expr::IfLet(pat, scrut, then, els, span) => (
                self.light_presence_binding_decision(*span, pat, scrut, env, props),
                then,
                els,
            ),
            _ => return false,
        };
        match decision {
            Some(true) => block_always_returns(then),
            Some(false) => match els.as_deref() {
                None => false,
                Some(Expr::Block(b, _)) => block_always_returns(b),
                Some(nested @ Expr::If(..)) => self.light_if_chain_diverges(nested, env, props),
                Some(_) => false,
            },
            None => false,
        }
    }

    fn infer_returns_expr(
        &mut self,
        expr: &Expr,
        env: &mut ScopeStack,
        normal: &mut Vec<(Type, Span)>,
        props: &mut LightProps,
    ) {
        match expr {
            Expr::If(cond, then, els, span) => {
                // A decided type or member-presence test walks the selected
                // arm only: the other arm's returns and error sites belong to
                // other instances.
                if let Some(matched) = self.light_condition_decision(*span, cond, env, props) {
                    if matched {
                        self.infer_returns_block(then, &mut env.clone(), normal, props);
                    } else if let Some(els) = els {
                        self.infer_returns_expr(els, &mut env.clone(), normal, props);
                    }
                    return;
                }
                self.infer_expr_light(cond, env, props);
                self.infer_returns_block(then, &mut env.clone(), normal, props);
                if let Some(els) = els {
                    self.infer_returns_expr(els, &mut env.clone(), normal, props);
                }
            }
            Expr::IfLet(pat, scrut, then, els, span) => {
                let decision = self.light_presence_binding_decision(*span, pat, scrut, env, props);
                if decision != Some(false) {
                    let scrut_ty = self.infer_expr_light(scrut, env, props);
                    let mut inner = self.light_pattern_scope(pat, &scrut_ty, env, true);
                    self.infer_returns_block(then, &mut inner, normal, props);
                }
                if decision != Some(true)
                    && let Some(els) = els
                {
                    self.infer_returns_expr(els, &mut env.clone(), normal, props);
                }
            }
            Expr::Match(scrut, arms, _) => {
                let scrut_ty = self.infer_expr_light(scrut, env, props);
                for arm in arms {
                    let mut inner = self.light_pattern_scope(&arm.pattern, &scrut_ty, env, false);
                    self.infer_returns_expr(&arm.body, &mut inner, normal, props);
                }
            }
            Expr::Block(block, _) => {
                self.infer_returns_block(block, &mut env.clone(), normal, props)
            }
            other => {
                self.infer_expr_light(other, env, props);
            }
        }
    }

    /// If `expr` is `recv.push(value)` or `recv.insert(idx, value)` where `recv`
    /// is a slice/array, unify its element type with the pushed value's type.
    /// This pins the (fresh, local) element variable of a collection being built
    /// up, so the light return-inference pass sees the grown element type. It
    /// only ever binds the local's own element variable, not the function's
    /// parameter variables.
    fn track_collection_growth(&mut self, expr: &Expr, env: &ScopeStack, props: &mut LightProps) {
        if let Expr::Call(callee, args, _) = expr
            && let Expr::Field(recv, method, _) = callee.as_ref()
            && !callee.span().is_parenthesized()
            && matches!(method.as_str(), "push" | "insert")
            && let Some(value_arg) = args.last()
        {
            let recv_ty = self.infer_expr_light(recv, env, props);
            if let Some(elem) = brass_hir::index_element(&self.resolve(&recv_ty)) {
                let value_ty = self.infer_expr_light(&value_arg.expr, env, props);
                let _ = self.solver.unify(&elem, &value_ty);
            }
        }
    }

    /// The light type of `expr` in `env`, recording its propagation sites in
    /// `props`. What the walk cannot type is a fresh unknown, never an error.
    pub(super) fn infer_expr_light(
        &mut self,
        expr: &Expr,
        env: &ScopeStack,
        props: &mut LightProps,
    ) -> Type {
        match expr {
            Expr::Int(v, _) => int_literal_type(*v),
            Expr::Float(..) => Type::Float(FloatKind::F64),
            Expr::Bool(..) => Type::Bool,
            Expr::Null(_) => Type::null(),
            Expr::Str(..) => Type::Str,
            Expr::Ident(name, _) => match self.lookup(env, name) {
                Some(t) => self.instantiate_closure_scheme_light(t),
                None => self.fresh_unknown(),
            },
            Expr::SelfExpr(_) => self
                .lookup(env, "self")
                .unwrap_or_else(|| self.fresh_unknown()),
            Expr::Unary(..) if let Some(value) = expr.int_literal_value() => {
                int_literal_type(value)
            }
            Expr::Unary(_, inner, _) => self.infer_expr_light(inner, env, props),
            // A type test's value is a compile-time bool; an `if` on one is
            // decided by `light_condition_decision`.
            Expr::TypeTest(..) => Type::Bool,
            Expr::Binary(op, left, right, _) => {
                let left_ty = self.infer_expr_light(left, env, props);
                let right_ty = self.infer_expr_light(right, env, props);
                self.infer_binary_light(*op, (left, left_ty), (right, right_ty))
            }
            Expr::Call(callee, args, _) => self.infer_call_light(callee, args, env, props),
            Expr::Field(base, name, _) => self.infer_field_light(base, name, env, props),
            Expr::Index(base, _, _) => match self.infer_expr_light(base, env, props) {
                ref bt if brass_hir::index_element(bt).is_some() => {
                    brass_hir::index_element(bt).unwrap()
                }
                Type::Str => Type::Str,
                _ => self.fresh_unknown(),
            },
            Expr::ErrorProp(inner, span) => {
                let ty = self.infer_expr_light(inner, env, props);
                let ty = self.resolve(&ty);
                if let Some((ok, err)) = ty.result_payloads() {
                    {
                        let lifted = crate::lift_err_payload(self.program, self.resolve(err));
                        props.errors.push((lifted, *span));
                    }
                    ok.clone()
                } else if let Type::Nullable(inner_ty) = &ty {
                    // `e!` on a nullable unwraps the value; the null case
                    // returns null from the enclosing callable, whose return
                    // type therefore gains an outer `?` (no error payload).
                    props.nulls.push(*span);
                    (**inner_ty).clone()
                } else if let Some(err) = self.full_err_props.get(span).cloned() {
                    // The full check of this body found a `Result` here that
                    // this walk cannot see (a callee fallible only at this
                    // instance): the site propagates its error all the same.
                    props.errors.push((err, *span));
                    self.fresh_unknown()
                } else {
                    // An operand of a type this walk could not determine (an
                    // unannotated parameter's method, say) may still be a
                    // `Result` in every instance: the body may be fallible.
                    props.open_errors |= ty.is_unknown();
                    self.fresh_unknown()
                }
            }
            Expr::Closure(params, body, span) => {
                let mut inner = env.clone();
                inner.push(Scope::default());
                let mut param_types = Vec::with_capacity(params.len());
                let provisional = self
                    .application_probe
                    .as_ref()
                    .filter(|probe| probe.assignment == Some(*span))
                    .map(|probe| probe.parameters.clone());
                for (index, param) in params.iter().enumerate() {
                    let ty = param
                        .ty
                        .as_ref()
                        .and_then(|t| self.resolve_type(t).ok())
                        .or_else(|| {
                            provisional
                                .as_ref()
                                .and_then(|types| types.get(index).cloned())
                        })
                        .unwrap_or_else(|| self.fresh_unknown());
                    param_types.push(ty.clone());
                    if param.name != "_" {
                        inner
                            .last_mut()
                            .expect("closure scope frame")
                            .insert(param.name.clone(), ty);
                    }
                }
                // The closure is its OWN callable: its error/null sites shape
                // the closure's return, never the enclosing function's. The
                // caller's `props` stays untouched: threading it through would
                // wrap the PARENT's inferred return in the closure's `Result`,
                // though the propagation returns from the closure alone.
                let mut own = LightProps::default();
                let ret = self.infer_expr_light(body, &inner, &mut own);
                let ret = if own.errors.is_empty() {
                    ret
                } else {
                    self.result_from_payloads(Some(ret), &own.errors, false)
                };
                let ret = super::precompute::wrap_null_propagated_return(ret, &own.nulls);
                let (ret, identity) = self.inferred_closure_result(ret);
                self.remember_closure(expr, &param_types, env, false, identity);
                Type::Fun(param_types, Box::new(ret))
            }
            Expr::Array(items, _) => {
                let elem_tys: Vec<Type> = items
                    .iter()
                    .map(|e| self.infer_expr_light(e, env, props))
                    .collect();
                // Mirror the full check's array-vs-tuple classification and its
                // null handling. The light pass gives the globals their
                // provisional types (see `precompute_global_bindings`), which the
                // method co-check reads before the initializers' full check
                // settles them: a global typed `int32[]` here where the full
                // check builds a tuple would be read at the wrong type.
                if let Some(tuple) = self.tuple_of_elements(items, &elem_tys) {
                    Type::Tuple(tuple)
                } else {
                    let base = self
                        .numeric_element_type(items, &elem_tys)
                        .or_else(|| {
                            elem_tys
                                .iter()
                                .zip(items)
                                .find(|(_, e)| !matches!(e, Expr::Null(_)))
                                .map(|(t, _)| t.clone())
                        })
                        .unwrap_or_else(|| self.fresh_empty_array_elem());
                    let saw_null = items.iter().any(|e| matches!(e, Expr::Null(_)));
                    if saw_null && !matches!(self.resolve(&base), Type::Nullable(_)) {
                        Type::Slice(Box::new(Type::Nullable(Box::new(base))))
                    } else {
                        Type::Slice(Box::new(base))
                    }
                }
            }
            // Mirror the full check's range rule: the element type is the
            // bounds' common integer type, a literal bound adapting to the
            // other side (so `[0..n]` follows `n`'s width, not the literal's).
            Expr::Range(lo, hi, _) => {
                let lo_ty = self.infer_expr_light(lo, env, props);
                let hi_ty = self.infer_expr_light(hi, env, props);
                let lo_r = peel_value_wrappers(&self.resolve(&lo_ty)).clone();
                let hi_r = peel_value_wrappers(&self.resolve(&hi_ty)).clone();
                let elem = brass_typesys::common_operand_type(
                    brass_typesys::NumericOperand::new(
                        &lo_r,
                        brass_typesys::NumericLiteral::of_expr(lo),
                    ),
                    brass_typesys::NumericOperand::new(
                        &hi_r,
                        brass_typesys::NumericLiteral::of_expr(hi),
                    ),
                )
                .unwrap_or(lo_r);
                Type::Slice(Box::new(elem))
            }
            Expr::TypeLit(name, fields, _) => self.infer_type_lit_light(name, fields, env, props),
            Expr::VariantLit(name, variant, fields, _) => {
                self.infer_variant_lit_light(name, variant, fields, env, props)
            }
            Expr::If(cond, then, els, span) => {
                // A decided type or member-presence test types as the selected
                // arm alone; the unselected arm is other instances' code (no
                // join, no props).
                if let Some(matched) = self.light_condition_decision(*span, cond, env, props) {
                    return if matched {
                        self.infer_block_value_light(then, &mut env.clone(), props)
                    } else {
                        els.as_ref()
                            .map(|e| self.infer_expr_light(e, env, props))
                            .unwrap_or(Type::Void)
                    };
                }
                let then_ty = self.infer_block_value_light(then, &mut env.clone(), props);
                let else_ty = els
                    .as_ref()
                    .map(|e| self.infer_expr_light(e, env, props))
                    .unwrap_or(Type::Void);
                self.branch_join_light(then, els.as_deref(), then_ty, else_ty)
            }
            Expr::IfLet(pat, scrut, then, els, span) => {
                let decision = self.light_presence_binding_decision(*span, pat, scrut, env, props);
                if decision == Some(false) {
                    return els
                        .as_ref()
                        .map(|e| self.infer_expr_light(e, env, props))
                        .unwrap_or(Type::Void);
                }
                let scrut_ty = self.infer_expr_light(scrut, env, props);
                let mut inner = self.light_pattern_scope(pat, &scrut_ty, env, true);
                let then_ty = self.infer_block_value_light(then, &mut inner, props);
                if decision == Some(true) {
                    return then_ty;
                }
                let else_ty = els
                    .as_ref()
                    .map(|e| self.infer_expr_light(e, env, props))
                    .unwrap_or(Type::Void);
                self.branch_join_light(then, els.as_deref(), then_ty, else_ty)
            }
            Expr::Match(scrut, arms, _) => {
                let scrut_ty = self.infer_expr_light(scrut, env, props);
                let values: Vec<(Type, Option<brass_typesys::NumericLiteral>)> = arms
                    .iter()
                    .map(|arm| {
                        let inner = self.light_pattern_scope(&arm.pattern, &scrut_ty, env, false);
                        let ty = self.infer_expr_light(&arm.body, &inner, props);
                        (ty, value_literal(&arm.body))
                    })
                    .collect();
                if let Some(joined) = self.numeric_branch_join(&values) {
                    return joined;
                }
                let tys: Vec<Type> = values.into_iter().map(|(ty, _)| ty).collect();
                self.common_type_list(&tys)
                    .unwrap_or_else(|| self.fresh_unknown())
            }
            Expr::Block(block, _) => self.infer_block_value_light(block, &mut env.clone(), props),
        }
    }

    fn infer_call_light(
        &mut self,
        callee: &Expr,
        args: &[Arg],
        env: &ScopeStack,
        props: &mut LightProps,
    ) -> Type {
        if let Expr::Ident(name, _) = callee {
            // Mirror the full check's `error(x)` typing (the prelude Error
            // wrap; see `check_call`) so entries assembled by this pass carry
            // the same payload shape.
            if name == "error" {
                let value_ty = args
                    .first()
                    .map(|a| self.infer_expr_light(&a.expr, env, props))
                    .unwrap_or(Type::Void);
                for a in args.iter().skip(1) {
                    self.infer_expr_light(&a.expr, env, props);
                }
                // A program without the prelude has no `Error`: the payload
                // is the raw value.
                let err_ty = match self.program.prelude_type("Error") {
                    Some(err_info) => {
                        let mut err = NominalType::new(err_info.id, &err_info.name);
                        err.substitution.insert("value", self.resolve(&value_ty));
                        Type::Record(err)
                    }
                    None => self.resolve(&value_ty),
                };
                // Every `error(..)` the body evaluates is one of its error
                // sources -- returned, propagated, or bound -- so the body
                // is fallible and its payload joins the error type, as MIR
                // lowering (`brass_mir::fallible_block`) and monomorphization
                // count it.
                props.errors.push((err_ty.clone(), callee.span()));
                let ok = self.fresh_unknown();
                return Type::result(ok, err_ty);
            }
            // A builtin name (and a prelude name typed as one: `print`,
            // `assert`, ...) takes that shortcut only when the call reaches it;
            // a local binding or a user function of the name shadows it.
            let builtin = if self.calls_prelude_function(name, self.lookup(env, name).is_some()) {
                self.builtin_function_type_light(name)
            } else {
                None
            };
            if let Some(ret) = builtin {
                args.iter().for_each(|arg| {
                    self.infer_expr_light(&arg.expr, env, props);
                });
                return ret;
            }
            // A binding in scope -- a parameter, a local closure, a global --
            // shadows a same-named top-level function, exactly as the full
            // check resolves the callee (`check_call`): `helper()` on a closure
            // parameter `helper` is not the unrelated `fun helper`'s result.
            // A function value returns its own function type's result: a
            // fallible closure's `Result` makes a `!` on the call an error site
            // of this body, so the instance is fallible -- whether or not the
            // unwrapped value reaches a return.
            if let Some(local) = self.lookup(env, name) {
                if self.probe_application(&local, args, env, props) {
                    return self.fresh_unknown();
                }
                let local = self.instantiate_closure_scheme_light(local);
                let arguments: Vec<_> = args
                    .iter()
                    .map(|arg| self.infer_expr_light(&arg.expr, env, props))
                    .collect();
                return self
                    .infer_callable_light(&local, &arguments)
                    .unwrap_or_else(|| self.fresh_unknown());
            }
            // The table is keyed by SYMBOL. A bare unique name is its own symbol, but
            // a module-qualified call (`percent.decode`, which the resolve pass
            // rewrote to a dotted marker) and a renamed import are not -- and a
            // missed lookup here would cost the caller its whole error type: the
            // `!` on the call would record an unknown Err.
            let symbol = self
                .lookup_function(name)
                .map(|f| f.symbol.clone())
                .or_else(|| {
                    self.function_returns
                        .contains_key(name)
                        .then(|| name.clone())
                });
            if let Some(ret) = symbol.and_then(|s| self.read_function_return(&s)) {
                args.iter().for_each(|arg| {
                    self.infer_expr_light(&arg.expr, env, props);
                });
                return ret;
            }
        }
        if let Expr::Field(base, method, _) = callee
            && !callee.span().is_parenthesized()
        {
            if let Some(qualifier) = self.static_call_qualifier(base, method, env) {
                let ret = self.primitive_static_type(&qualifier, method);
                if ret.is_some() {
                    args.iter().for_each(|arg| {
                        self.infer_expr_light(&arg.expr, env, props);
                    });
                }
                if let Some(ret) = ret {
                    return ret;
                }
                // A user type's STATIC method (`File.open(..)`, `HttpClient.http(..)`):
                // the base names a type rather than a value, so there is no receiver
                // to infer and the receiver-keyed lookup below cannot fire.
                //
                // A fully-known annotation IS the answer. Otherwise -- an unannotated
                // constructor, or a `T!` whose Err payload the annotation leaves open
                // -- the precompute table has it, and is read FRESHENED. That table
                // holds the variables of one shared instantiation, so handing it over
                // verbatim would let the first call site that constrains them pin them
                // for every other: a witness-free `HashMap.new()`, whose key/value
                // slots are meant to be fixed by each binding's own use, would take
                // the first `set` in the program and leave every later binding
                // unrefined. Fresh variables per site keep that inference intact while
                // still telling the light pass WHICH type the call built -- without
                // which a local bound from a constructor would stay unknown, every
                // method called on it would be unknown too, and a caller of
                // `File.open(..)!` could not see the Err type it propagates.
                // Resolved MODULE-AWARE, not by bare key: a type whose name is also
                // declared elsewhere (an alias in one module named like another
                // module's nominal) has only module-qualified symbols, and a missed
                // lookup would type the call as unknown, losing the caller's whole
                // inferred fallibility.
                if let Some(resolved) = self.method_for_qualifier(&qualifier, method) {
                    let declared = resolved.signature.ret_ty.clone();
                    let ret = match &declared {
                        Some(ty) if brass_hir::is_fully_known(ty) => declared,
                        _ => {
                            let key = (resolved.qualifier.clone(), method.clone());
                            let from_table = self.read_method_return(&key).map(|ty| {
                                let ty = self.resolve(&ty);
                                self.freshen(&ty)
                            });
                            // A CONSTRUCTOR (`HashMap.new()`) is rebuilt from the
                            // type's SCHEME rather than taken from the table. The
                            // light pass infers the constructor's body without the
                            // scheme, so its `Self { .. }` carries the field types it
                            // could see there (`_entries: never?[]`, from a slot array
                            // sized with `null`) rather than the ones the scheme
                            // expresses over the type's parameters
                            // (`_Entry<key, value>?[]`). That shape is not merely
                            // imprecise, it is a DIFFERENT type: nothing can pin the
                            // element types through it, and it does not even unify
                            // with what the full check builds. A fresh scheme instance
                            // is what the full check hands back.
                            let instance = from_table
                                .as_ref()
                                .map(|ty| self.resolve(ty))
                                .and_then(|ty| self.fresh_scheme_instance(&ty));
                            instance.or(from_table).or(declared)
                        }
                    };
                    if let Some(ret) = ret {
                        args.iter().for_each(|arg| {
                            self.infer_expr_light(&arg.expr, env, props);
                        });
                        return ret;
                    }
                }
            }
            let recv = self.infer_expr_light(base, env, props);
            if method == "context"
                && let Type::Nullable(inner) = self.resolve(&recv)
            {
                args.iter().for_each(|arg| {
                    self.infer_expr_light(&arg.expr, env, props);
                });
                let inner = *inner;
                if matches!(&inner, Type::Sum(result) if result.id == brass_hir::RESULT_TYPE_ID) {
                    return inner;
                }
                let error = match self.program.prelude_type("Error") {
                    Some(info) => {
                        let mut error = NominalType::new(info.id, &info.name);
                        error.substitution.insert("value", Type::Str);
                        Type::Record(error)
                    }
                    None => Type::Str,
                };
                return Type::result(inner, error);
            }
            // A user method's precomputed return: methods of a nominal
            // receiver (peeling a narrowed nullable) resolve through the same
            // table the full pass consults, so a body that propagates another
            // type's fallible method infers fallible itself. The precompute
            // fixpoint re-infers a reader when an entry it read changes, so a
            // cross-type chain sees its callee's entry.
            let peeled = match self.resolve(&recv) {
                Type::Nullable(inner) => *inner,
                other => other,
            };
            if let Type::Record(n) | Type::Sum(n) = &peeled
                && let Some(info) = self.program.type_by_id(n.id)
                && let Some(qualifier) = match &info.kind {
                    TypeKind::Record { .. } => Some(info.symbol.clone()),
                    TypeKind::Sum { variants } => variants
                        .iter()
                        .find(|variant| variant.methods.contains_key(method))
                        .map(|variant| format!("{}.{}", info.symbol, variant.name)),
                }
                && let Some(ret) = self.read_method_return(&(qualifier, method.clone()))
            {
                args.iter().for_each(|arg| {
                    self.infer_expr_light(&arg.expr, env, props);
                });
                return ret;
            }
        }
        let callable = self.infer_expr_light(callee, env, props);
        let arguments: Vec<_> = args
            .iter()
            .map(|arg| self.infer_expr_light(&arg.expr, env, props))
            .collect();
        self.infer_callable_light(&callable, &arguments)
            .unwrap_or_else(|| self.fresh_unknown())
    }

    /// A fresh instance of `ty`'s nominal built from its SCHEME: every scheme
    /// parameter takes its own variable, and each field is the scheme's field type
    /// over them. `None` when `ty` is not a record with a scheme.
    ///
    /// Restricted to a record with declared type SLOTS (`type key`). Those are the
    /// witness-free containers whose element types a use has to pin, and whose
    /// constructor the light pass gets wrong. Every other record's fields are
    /// whatever its constructor built, and the scheme's view of them -- a
    /// generalization over the co-checked bodies -- is not the same thing: rebuilding
    /// an `HttpClient` from it replaces the closure its `_connect` field actually
    /// holds.
    fn fresh_scheme_instance(&mut self, ty: &Type) -> Option<Type> {
        let Type::Record(n) = ty else {
            return None;
        };
        let info = self.program.type_by_id(n.id)?;
        if info.slots.is_empty() {
            return None;
        }
        let scheme = self.schemes.get(&info.symbol)?.clone();
        let mut map: HashMap<u32, Type> = HashMap::default();
        for p in &scheme.params {
            let fresh = self.fresh_unknown();
            map.insert(*p, fresh);
        }
        let mut subst = brass_hir::Substitution::empty();
        for (name, fty) in &scheme.fields {
            subst.insert(
                name.clone(),
                super::instantiate::apply_scheme_param_map(fty, &map),
            );
        }
        Some(Type::Record(brass_hir::NominalType::with_substitution(
            n.id,
            n.name().to_string(),
            subst,
        )))
    }

    fn infer_field_light(
        &mut self,
        base: &Expr,
        name: &str,
        env: &ScopeStack,
        props: &mut LightProps,
    ) -> Type {
        let shadowed = matches!(base, Expr::Ident(n, _) if self.lookup(env, n).is_some());
        if let Some(ty) = self.unit_variant_type(base, name, shadowed) {
            return ty;
        }
        // Resolve the base before matching: an indexed element or other
        // intermediate may still be an open inference variable that the solver has
        // since pinned to a record (e.g. `self._entries[idx]` is the map's entry
        // type once a `push` fixed it). Without resolving, the match falls through
        // and the field type is lost as a fresh unknown.
        let base_ty = self.infer_expr_light(base, env, props);
        match self.resolve(&base_ty) {
            Type::Record(record) => record.substitution.get(name).cloned().unwrap_or_else(|| {
                self.program
                    .type_by_id(record.id)
                    .and_then(|info| match &info.kind {
                        TypeKind::Record { fields, .. } => fields.iter().find(|f| f.name == name),
                        TypeKind::Sum { .. } => None,
                    })
                    .and_then(|f| f.resolved_ty.clone())
                    .unwrap_or_else(|| self.fresh_unknown())
            }),
            Type::Sum(sum) => self
                .self_variant_field_type(base, &sum, name)
                .or_else(|| self.common_sum_field_type(&sum, name))
                .unwrap_or_else(|| self.fresh_unknown()),
            _ => self.fresh_unknown(),
        }
    }

    fn infer_type_lit_light(
        &mut self,
        name: &str,
        fields: &[(String, Expr)],
        env: &ScopeStack,
        props: &mut LightProps,
    ) -> Type {
        if name.is_empty() {
            let field_tys: Vec<(String, Type)> = fields
                .iter()
                .map(|(fname, e)| (fname.clone(), self.infer_expr_light(e, env, props)))
                .collect();
            return brass_hir::structural_record(field_tys);
        }
        let tn = self.resolve_self_name(name);
        // A `type A = R { .. }` alias names `R` at the alias's instance.
        let head = match self.resolve_type_symbol(&tn) {
            Some(symbol) => self.program.types.get(&symbol).map(|info| (info, None)),
            None => match self.resolve_alias(&tn) {
                Some(alias @ Type::Record(_)) => {
                    let Type::Record(n) = &alias else {
                        unreachable!("matched a record alias");
                    };
                    self.program
                        .type_by_id(n.id)
                        .map(|info| (info, Some(alias)))
                }
                _ => None,
            },
        };
        let resolved = head.and_then(|(info, alias)| {
            let TypeKind::Record { fields, .. } = &info.kind else {
                return None;
            };
            Some((alias.unwrap_or_else(|| info.type_ref()), fields.clone()))
        });
        let Some((ret, declared)) = resolved else {
            fields.iter().for_each(|(_, expr)| {
                self.infer_expr_light(expr, env, props);
            });
            return self.fresh_unknown();
        };
        let substitution = self.infer_lit_field_substitution(None, &declared, fields, env, props);
        match &ret {
            // An alias's pinned entries stay: the literal is built at its
            // instance (the full check adapts the values to them).
            Type::Record(n) if !n.substitution.is_empty() => {
                let mut entries = substitution;
                for (key, pinned) in n.substitution.iter() {
                    entries.insert(key, pinned.clone());
                }
                overlay_nominal_substitution(ret, &entries)
            }
            _ => apply_nominal_substitution(ret, substitution),
        }
    }

    fn infer_variant_lit_light(
        &mut self,
        type_name: &str,
        variant: &str,
        fields: &[(String, Expr)],
        env: &ScopeStack,
        props: &mut LightProps,
    ) -> Type {
        let tn = self.resolve_self_name(type_name);
        let resolved = self
            .resolve_sum_head_symbol(&tn)
            .and_then(|symbol| self.program.types.get(&symbol))
            .and_then(|info| {
                let variant = info.variant(variant)?;
                Some((info.type_ref(), variant.fields.clone()))
            });
        let Some((ret, declared)) = resolved else {
            fields.iter().for_each(|(_, expr)| {
                self.infer_expr_light(expr, env, props);
            });
            return self.fresh_unknown();
        };
        let substitution =
            self.infer_lit_field_substitution(Some(variant), &declared, fields, env, props);
        apply_nominal_substitution(ret, substitution)
    }

    fn infer_lit_field_substitution(
        &mut self,
        variant: Option<&str>,
        declared: &[brass_hir::FieldInfo],
        fields: &[(String, Expr)],
        env: &ScopeStack,
        props: &mut LightProps,
    ) -> Substitution {
        let mut substitution = Substitution::empty();
        for field in declared {
            if let Some((_, expr)) = fields.iter().find(|(name, _)| name == &field.name) {
                let got = self.infer_expr_light(expr, env, props);
                // A field whose declared type carries any inference variable --
                // a bare dynamic field, or one written over the declaration's
                // type SLOTS (`items: Self.item[]`) -- is per-instance: record
                // the value's own type so a later use of this instance (a
                // `push` this pass growth-tracks, a field read) resolves
                // through the substitution rather than falling back to the
                // declaration's SHARED variables. Pinning those couples every
                // literal of the type program-wide, in the solver this pass
                // shares with the full check.
                let dynamic = field
                    .resolved_ty
                    .as_ref()
                    .is_some_and(|t| !brass_hir::type_vars(t).is_empty());
                if dynamic {
                    substitution.insert(field_substitution_key(variant, &field.name), got);
                }
            }
        }
        substitution
    }

    fn infer_block_value_light(
        &mut self,
        block: &Block,
        env: &mut ScopeStack,
        props: &mut LightProps,
    ) -> Type {
        let mut last = Type::Void;
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let {
                    pat,
                    ty,
                    value,
                    is_const,
                    ..
                } => {
                    let ty =
                        self.light_let_type(ty.as_ref(), value.as_ref(), *is_const, env, props);
                    self.bind_pattern_light(pat, &ty, env);
                    last = Type::Void;
                }
                Stmt::Expr(expr) => last = self.infer_expr_light(expr, env, props),
                Stmt::Return(Some(expr), _) => return self.infer_expr_light(expr, env, props),
                _ => last = Type::Void,
            }
        }
        last
    }

    /// The type a `let` (or `const`, `is_const`) binds in the light pass,
    /// mirroring the full check's `check_stmt`: an annotation is the binding's
    /// type (instantiated against the initializer, so an `infer` slot still
    /// takes the value's type), and only an unannotated binding takes its
    /// initializer's type -- a fixed-length array for an unannotated `const`
    /// bound directly to a non-empty array literal. Typing `let x: int64 = 5`
    /// from the literal alone would make a later `return x` look like an
    /// `int32`.
    pub(super) fn light_let_type(
        &mut self,
        annotation: Option<&TypeExpr>,
        value: Option<&Expr>,
        is_const: bool,
        env: &ScopeStack,
        props: &mut LightProps,
    ) -> Type {
        let value_ty = value.map(|v| self.infer_expr_light(v, env, props));
        let annotated = annotation.and_then(|te| self.light_annotation(te, env));
        match (annotated, value_ty) {
            (Some(annotated), Some(value_ty)) => {
                self.instantiate_annotated_type(&annotated, &value_ty)
            }
            (Some(annotated), None) => annotated,
            (None, Some(Type::Slice(elem))) if is_const => match value {
                Some(Expr::Array(items, _)) if !items.is_empty() => Type::Array(elem, items.len()),
                _ => Type::Slice(elem),
            },
            (None, Some(value_ty)) => value_ty,
            // The parser only omits an initializer under an annotation.
            (None, None) => Type::Unknown(brass_hir::INFER_VAR),
        }
    }

    /// Resolve a local annotation for the light pass. A `typeof(v)` node takes
    /// `v`'s light type (the full check's `resolve_annotation_scoped` ties it
    /// the same way); its operand is never evaluated, so whatever propagation
    /// it mentions is not a site of the enclosing body. `None` when the
    /// annotation does not resolve -- the full check reports that.
    fn light_annotation(&mut self, te: &TypeExpr, env: &ScopeStack) -> Option<Type> {
        if !contains_typeof(te) {
            return self.resolve_type(te).ok();
        }
        match te {
            TypeExpr::TypeOf(e, _) => {
                Some(self.infer_expr_light(e, env, &mut LightProps::default()))
            }
            TypeExpr::Nullable(inner, _) => {
                Some(Type::nullable(self.light_annotation(inner, env)?))
            }
            TypeExpr::Array(inner, Some(n), _) => Some(Type::Array(
                Box::new(self.light_annotation(inner, env)?),
                *n,
            )),
            TypeExpr::Array(inner, None, _) => {
                Some(Type::Slice(Box::new(self.light_annotation(inner, env)?)))
            }
            TypeExpr::Fallible(inner, _) => {
                let ok = self.light_annotation(inner, env)?;
                let err = self.fresh_unknown();
                Some(self.scoped_result(ok, err, Span::new(0, 0)))
            }
            TypeExpr::Mut(inner, _) => {
                Some(Type::Mut(Box::new(self.light_annotation(inner, env)?)))
            }
            TypeExpr::Ref(inner, _) => {
                Some(Type::Ref(Box::new(self.light_annotation(inner, env)?)))
            }
            TypeExpr::Tuple(elems, _) => elems
                .iter()
                .map(|e| self.light_annotation(e, env))
                .collect::<Option<Vec<_>>>()
                .map(Type::Tuple),
            _ => self.resolve_type(te).ok(),
        }
    }

    /// The scope an `if let` arm or a `match` arm body is walked in: the
    /// enclosing environment plus the pattern's bindings at the scrutinee's
    /// type. A binding shadows any outer local, parameter or global of the same
    /// name inside the arm: `name` in `match p { P { name } => name }` is the
    /// field, not an outer `let name = 0`.
    /// `presence` marks an `if let`, where a plain binding on a nullable
    /// scrutinee is a presence test binding the unwrapped value (as in the full
    /// check).
    fn light_pattern_scope(
        &mut self,
        pat: &Pattern,
        scrut_ty: &Type,
        env: &ScopeStack,
        presence: bool,
    ) -> ScopeStack {
        let mut inner = env.clone();
        inner.push(Scope::default());
        let resolved = self.resolve(scrut_ty);
        let bind_ty = match (pat, peel_ref_mut(&resolved)) {
            (Pattern::Binding(_, None, _), Type::Nullable(value)) if presence => (**value).clone(),
            _ => scrut_ty.clone(),
        };
        self.bind_pattern_light(pat, &bind_ty, &mut inner);
        inner
    }

    /// The light type of a two-branch `if`/`if let`: numeric branches join
    /// by the full check's rule (a literal branch adapts), anything else
    /// keeps the then-branch type when the two agree.
    fn branch_join_light(
        &mut self,
        then: &Block,
        els: Option<&Expr>,
        then_ty: Type,
        else_ty: Type,
    ) -> Type {
        let branches = [
            (then_ty, block_literal(then)),
            (else_ty, els.and_then(value_literal)),
        ];
        if let Some(joined) = self.numeric_branch_join(&branches) {
            return joined;
        }
        let [(then_ty, _), (else_ty, _)] = branches;
        self.common_type_or_unknown(then_ty, else_ty)
    }

    /// Type a binary operator best-effort. Two numbers follow the shared
    /// operator rule (`brass_typesys::numeric_binary`), so a body's light
    /// return type matches the one the full check and monomorphization give
    /// (`b + 1` with `b: uint8` is `uint8`); anything else keeps the operand
    /// type when the two unify, and is left open otherwise.
    fn infer_binary_light(
        &mut self,
        op: BinOp,
        (left_expr, left): (&Expr, Type),
        (right_expr, right): (&Expr, Type),
    ) -> Type {
        if matches!(
            op,
            BinOp::Eq
                | BinOp::Ne
                | BinOp::Lt
                | BinOp::Gt
                | BinOp::Le
                | BinOp::Ge
                | BinOp::And
                | BinOp::Or
        ) {
            return Type::Bool;
        }
        let (l, r) = (self.resolve(&left), self.resolve(&right));
        let (left_literal, right_literal) = (
            brass_typesys::NumericLiteral::of_expr(left_expr),
            brass_typesys::NumericLiteral::of_expr(right_expr),
        );
        // An open operand next to a float literal is computed in `float64`
        // when it turns out to be an integer: the result is not the operand's
        // type, so it stays open (as in the full check).
        let float_literal = [left_literal, right_literal]
            .iter()
            .any(|lit| matches!(lit, Some(brass_typesys::NumericLiteral::Float(_))));
        match brass_typesys::numeric_binary(
            op,
            brass_typesys::NumericOperand::new(peel_ref_mut(&l), left_literal),
            brass_typesys::NumericOperand::new(peel_ref_mut(&r), right_literal),
        ) {
            Ok(typing) => typing.result,
            Err(brass_typesys::OperatorError::NotNumeric)
                if !float_literal && self.can_unify(&left, &right) =>
            {
                left
            }
            Err(_) => self.fresh_unknown(),
        }
    }

    /// The light join of `types` (`None` for none), left to right: `null` with
    /// `T` makes `T?`, a type that unifies with the running join leaves it as
    /// it is, and a conflict makes the join a fresh unknown.
    pub(super) fn common_type_list(&mut self, types: &[Type]) -> Option<Type> {
        let (first, rest) = types.split_first()?;
        let mut common = first.clone();
        for ty in rest {
            if let Some(nullable) = common_nullable_type(&common, ty) {
                common = nullable;
                continue;
            }
            if !self.can_unify(&common, ty) {
                return Some(self.fresh_unknown());
            }
        }
        Some(common)
    }

    /// Bind the names `pat` introduces, matched against a value of type `ty`,
    /// in the innermost frame of `env`.
    pub(super) fn bind_pattern_light(&mut self, pat: &Pattern, ty: &Type, env: &mut ScopeStack) {
        match pat {
            Pattern::Binding(name, None, _) if !self.is_unit_variant_name(name) => {
                env.last_mut()
                    .expect("light scope frame")
                    .insert(name.clone(), ty.clone());
            }
            Pattern::Record(variant, qualifier, fields, _) => {
                let ty = self.pattern_scrutinee_type(ty, variant, qualifier.as_ref());
                let field_types = self.pattern_field_types(&ty, variant);
                for field in fields {
                    let fty = field_types
                        .get(&field.name)
                        .cloned()
                        .unwrap_or_else(|| self.fresh_unknown());
                    if let Some(subpat) = &field.pat {
                        self.bind_pattern_light(subpat, &fty, env);
                    } else {
                        env.last_mut()
                            .expect("light scope frame")
                            .insert(field.name.clone(), fty);
                    }
                }
            }
            Pattern::Array(pats, _) => match self.resolve(ty) {
                Type::Tuple(elems) => {
                    for (pat, ety) in pats.iter().zip(&elems) {
                        self.bind_pattern_light(pat, ety, env);
                    }
                }
                Type::Array(inner, _) | Type::Slice(inner) => {
                    for pat in pats {
                        self.bind_pattern_light(pat, &inner, env);
                    }
                }
                // The subject's shape is not known here. Each position gets its OWN
                // variable, rather than the subject itself: the positions of a
                // destructuring are independent values, and binding every one to the
                // whole subject makes `[k, v]` claim that `k` and `v` each ARE the
                // pair -- so a `m.set(k, v)` pins the map's key and value to the
                // pair, and the map's element types come out as tuples.
                _ => {
                    for pat in pats {
                        let elem = self.fresh_unknown();
                        self.bind_pattern_light(pat, &elem, env);
                    }
                }
            },
            _ => {}
        }
    }
}
