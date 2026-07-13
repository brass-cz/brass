//! Expression typing below the `check_expr` hub: the main expression
//! dispatcher, expectation-directed checking (including closures
//! against a wanted function type), branch/block result joining,
//! place and condition typing, and iteration/indexing element types.

use super::*;

impl<'a> Checker<'a> {
    pub(super) fn check_expr_against(
        &mut self,
        expr: &Expr,
        want: &Type,
        scopes: &mut ScopeStack,
    ) -> Type {
        // An integer literal in an integer-typed required position takes that
        // type (resolution): record it at the target
        // kind so its runtime tag matches the annotation rather than defaulting
        // to int32 (typed literals).
        if let Some(v) = assign::literal_int_value(expr) {
            let target = match self.resolve(want) {
                Type::Int(k) => Some(k),
                Type::Nullable(inner) => match *inner {
                    Type::Int(k) => Some(k),
                    _ => None,
                },
                _ => None,
            };
            if let Some(k) = target
                && int_fits_kind(v, k)
            {
                let ty = Type::Int(k);
                self.record_expr_type(expr, &ty);
                return ty;
            }
        }
        if let (Expr::Array(items, span), Type::Array(elem, len)) = (expr, self.resolve(want)) {
            if items.len() != len {
                self.errors.push(TypeError {
                    message: format!(
                        "array literal has length {}, but `{}` requires length {}",
                        items.len(),
                        want.display(),
                        len
                    ),
                    span: *span,
                });
            }
            for item in items {
                let got = self.check_expr(item, scopes);
                self.expect_expr_assignable(&got, &elem, item);
            }
            let ty = Type::Array(elem, len);
            self.record_expr_type(expr, &ty);
            return ty;
        }
        // An array literal in a required slice position (`int32?[]`): each element
        // flows into the expected element type, so an integer literal takes the
        // annotated width, a `null` element is a valid nullable, and a plain value
        // widens to a nullable element. Propagating the element type is what lets
        // `[4, 1, 5, null, 65]` and `[4, 1, 5, 65]` both be `int32?[]` instead of
        // being inferred independently (a heterogeneous literal would otherwise
        // become a tuple).
        if let (Expr::Array(items, _), Type::Slice(elem)) = (expr, self.resolve(want)) {
            for item in items {
                self.check_expr_against(item, &elem, scopes);
            }
            let ty = Type::Slice(elem);
            self.record_expr_type(expr, &ty);
            return ty;
        }
        // A bracket literal in a required tuple position: each element flows into
        // its own expected type, so e.g. an int literal takes the annotated width.
        if let (Expr::Array(items, span), Type::Tuple(elems)) = (expr, self.resolve(want)) {
            if items.len() != elems.len() {
                self.errors.push(TypeError {
                    message: format!(
                        "tuple literal has {} elements, but `{}` requires {}",
                        items.len(),
                        want.display(),
                        elems.len()
                    ),
                    span: *span,
                });
            }
            for (item, ety) in items.iter().zip(&elems) {
                self.check_expr_against(item, ety, scopes);
            }
            let ty = Type::Tuple(elems);
            self.record_expr_type(expr, &ty);
            return ty;
        }
        // A closure in a position that wants a function type is checked against
        // that type: each parameter takes the expected parameter type (so an
        // unannotated `self`/value parameter is typed without a separate
        // annotation) and the body is checked against the expected return, so a
        // block-bodied closure's `return` reconciles with it rather than leaving
        // the closure's result `void`.
        if let Expr::Closure(params, body, _) = expr
            && let Type::Fun(want_params, want_ret) = self.resolve(want)
        {
            return self.check_closure_against(expr, params, body, &want_params, &want_ret, scopes);
        }
        // A call (or `call!`) in a required position keys a reflective
        // `-> infer!` method by `want`. Only these shapes can be keyed; set the
        // channel narrowly so it never leaks into an operand of a larger
        // expression (`check_call` takes it).
        let got = if matches!(expr, Expr::Call(..) | Expr::ErrorProp(..)) {
            let resolved = self.resolve(want);
            let saved = self.call_expected.replace(resolved);
            let g = self.check_expr(expr, scopes);
            self.call_expected = saved;
            g
        } else {
            self.check_expr(expr, scopes)
        };
        self.expect_expr_assignable(&got, want, expr);
        got
    }

    /// Check a closure literal against an expected function type, binding each
    /// parameter to the expected parameter type and the body to the expected
    /// return. Returns `Type::Fun(param_types, want_ret)`.
    fn check_closure_against(
        &mut self,
        expr: &Expr,
        params: &[Param],
        body: &Expr,
        want_params: &[Type],
        want_ret: &Type,
        scopes: &mut ScopeStack,
    ) -> Type {
        self.report_duplicate_params("closure", params);
        let mut closure_scope: HashMap<String, Type> = HashMap::new();
        let mut param_types = Vec::with_capacity(params.len());
        for (i, p) in params.iter().enumerate() {
            let expected = want_params
                .get(i)
                .cloned()
                .unwrap_or_else(|| self.fresh_unknown());
            // An explicit parameter annotation still applies and is checked
            // against the expected type; an unannotated parameter takes it.
            let ty = match &p.ty {
                Some(te) => {
                    let annotated = self
                        .resolve_type(te)
                        .unwrap_or_else(|_| self.fresh_unknown());
                    self.expect_assignable(&annotated, &expected, p.span);
                    annotated
                }
                None => expected,
            };
            closure_scope.insert(p.name.clone(), ty.clone());
            param_types.push(ty);
        }
        let mut inferred_env = env_from_scopes(scopes);
        inferred_env.extend(closure_scope.clone());
        let mut light_props = LightProps::default();
        self.infer_expr_light(body, &inferred_env, &mut light_props);
        let mut closure_scopes = scopes.clone();
        closure_scopes.push(closure_scope);
        self.const_scopes.push(HashSet::new());
        self.return_contexts
            .push(ReturnContext::Explicit(want_ret.clone()));
        self.return_values.push(Vec::new());
        let body_val = self.check_expr(body, &mut closure_scopes);
        self.return_values.pop();
        self.return_contexts.pop();
        self.const_scopes.pop();
        // An expression-bodied closure (not a `{ ... }` block) returns its body
        // value directly, so that value must match the expected return; a block
        // body returns through the `return` context handled above.
        if !matches!(body, Expr::Block(..)) {
            self.expect_expr_assignable(&body_val, want_ret, body);
        }
        let ty = Type::Fun(param_types, Box::new(want_ret.clone()));
        self.record_expr_type(expr, &ty);
        ty
    }

    fn check_error_propagation_return_context(&mut self, span: prepoly_parser::Span) {
        match self.return_contexts.last() {
            Some(ReturnContext::Inferred) => {}
            Some(ReturnContext::Explicit(ret)) if is_result_return_type(&self.resolve(ret)) => {}
            // The entry `main`'s OWN body (context depth 1: not a closure or a
            // re-checked callee inside it) may propagate regardless of its
            // annotation: a failed `!` there aborts the program with the error
            // instead of returning a `Result`.
            Some(ReturnContext::Explicit(_))
                if self.in_entry_main && self.return_contexts.len() == 1 => {}
            Some(ReturnContext::Explicit(ret)) => {
                self.errors.push(TypeError {
                    message: format!(
                        "error propagation requires `Result` return type, found `{}`",
                        self.resolve(ret).display()
                    ),
                    span,
                });
            }
            // Module top level: a failed `!` aborts the program with the
            // error, so propagation needs no enclosing fallible callable.
            None => {}
        }
    }

    /// `e!` on a NULLABLE operand returns null from the enclosing callable on
    /// the null case, so that callable's return must be able to be null: an
    /// inferred return (it gains an outer `?`), a nullable annotation, or a
    /// void one (statement use -- the null carries no observable value). The
    /// entry `main`'s own body and the module top level abort at runtime
    /// instead, so they need no such return type.
    fn check_null_propagation_return_context(&mut self, span: prepoly_parser::Span) {
        match self.return_contexts.last() {
            Some(ReturnContext::Inferred) | None => {}
            Some(ReturnContext::Explicit(_))
                if self.in_entry_main && self.return_contexts.len() == 1 => {}
            Some(ReturnContext::Explicit(ret)) => {
                let resolved = self.resolve(ret);
                if !matches!(resolved, Type::Nullable(_) | Type::Void) && !resolved.is_unknown() {
                    self.errors.push(TypeError {
                        message: format!(
                            "null propagation (`!` on a nullable) requires a nullable return type, found `{}`",
                            resolved.display()
                        ),
                        span,
                    });
                }
            }
        }
    }

    /// Record which way the `!` at `span` propagates in this elaboration, and
    /// reject a generic whose instantiations disagree. The `null_props` channel
    /// is a span SET consumed by ONE shared MIR lowering, so a `!` that
    /// unwraps a nullable in one instantiation and a `Result` in another has
    /// no single correct shape -- left alone, the null-propagation lowering is
    /// forced onto the `Result` instance, which then returns (or renders) the
    /// whole `Result` where its Ok payload was meant.
    fn record_prop_kind(&mut self, span: prepoly_parser::Span, kind: PropKind) {
        match self.prop_kinds.get(&span) {
            None => {
                self.prop_kinds.insert(span, Some(kind));
            }
            Some(Some(prev)) if *prev != kind => {
                self.errors.push(TypeError {
                    message: "`!` unwraps a nullable in one instantiation of this generic \
                              function and a `Result` in another; the two propagate \
                              differently, so `!` must resolve to one kind in every \
                              instantiation (annotate the parameter to fix it)"
                        .to_string(),
                    span,
                });
                // Mark reported: further instantiations reaching this span stay quiet.
                self.prop_kinds.insert(span, None);
            }
            _ => {}
        }
    }

    fn wrap_inferred_fallible_return(&mut self, ok: Type, props: &LightProps) -> Type {
        let base = if props.errors.is_empty() {
            ok
        } else {
            let err = self
                .reconcile_error_payloads(&props.errors, true)
                .unwrap_or_else(|| self.fresh_unknown());
            Type::result(ok, err)
        };
        super::precompute::wrap_null_propagated_return(base, &props.nulls)
    }

    pub(super) fn check_expr_inner(&mut self, e: &Expr, scopes: &mut ScopeStack) -> Type {
        match e {
            Expr::Int(v, _) => Type::Int(int_literal_kind(*v)),
            Expr::Float(_, _) => Type::Float(FloatKind::F64),
            Expr::Bool(_, _) => Type::Bool,
            Expr::Null(_) => Type::null(),
            Expr::Str(segs, _) => {
                for seg in segs {
                    if let StrSeg::Expr(e) = seg {
                        self.check_expr(e, scopes);
                    }
                }
                Type::Str
            }
            Expr::Ident(name, span) => {
                if let Some(t) = self.lookup(scopes, name) {
                    t
                } else if let Some(t) = self.lookup_aliased_global(name) {
                    // A global reached under an import rename or a module
                    // qualifier; the global scope holds it under its declared name.
                    t
                } else if self.is_resolvable_free_name(name) {
                    // A free function or runtime builtin used as a first-class
                    // value. Its precise function type is recovered at the call
                    // site; here we only need to accept the name as resolved.
                    self.fresh_unknown()
                } else {
                    // An undeclared value name. Name resolution is a hard
                    // pre-execution check, so this is an
                    // error rather than a fresh unknown that would launder into
                    // any required type and run as `void`.
                    self.errors.push(TypeError {
                        message: format!("unknown name `{name}`"),
                        span: *span,
                    });
                    self.fresh_unknown()
                }
            }
            Expr::SelfExpr(span) => scopes
                .iter()
                .rev()
                .find_map(|s| s.get("self").cloned())
                .or_else(|| self.self_type.as_ref().map(|s| self.type_by_name(s)))
                .unwrap_or_else(|| {
                    // `self` is only meaningful inside an instance method.
                    self.errors.push(TypeError {
                        message: "`self` is only valid inside a method".to_string(),
                        span: *span,
                    });
                    self.fresh_unknown()
                }),
            Expr::Unary(op, inner, span) => {
                let ty = self.check_expr(inner, scopes);
                self.check_unary(*op, &ty, *span)
            }
            Expr::Binary(op, a, b, span) => {
                let left = self.check_expr(a, scopes);
                let right = self.check_expr(b, scopes);
                self.check_binary_expr(*op, a, &left, b, &right, *span)
            }
            Expr::Call(callee, args, span) => self.check_call(callee, args, *span, scopes),
            Expr::Field(base, name, span) => self.check_field(base, name, *span, scopes),
            Expr::Index(base, idx, span) => {
                let base_ty = self.check_expr(base, scopes);
                let resolved = self.resolve(&base_ty);
                // A tuple is indexed by a constant literal, yielding the element
                // type at that position.
                if let Type::Tuple(elems) = &resolved {
                    let _ = self.check_expr(idx, scopes);
                    return match const_index(idx) {
                        Some(k) if (k as usize) < elems.len() => elems[k as usize].clone(),
                        Some(k) => {
                            self.errors.push(TypeError {
                                message: format!(
                                    "tuple index {k} out of bounds for `{}`",
                                    resolved.display()
                                ),
                                span: *span,
                            });
                            self.fresh_unknown()
                        }
                        None => {
                            self.errors.push(TypeError {
                                message: "a tuple can only be indexed by a constant integer"
                                    .to_string(),
                                span: *span,
                            });
                            self.fresh_unknown()
                        }
                    };
                }
                let idx_ty = self.check_expr(idx, scopes);
                self.expect_int_index(&idx_ty, idx.span());
                if let Some(elem) = prepoly_hir::index_element(&resolved) {
                    return elem;
                }
                match resolved {
                    Type::Str => Type::Str,
                    Type::Nullable(_) => {
                        self.report_nullable_use(*span);
                        self.fresh_unknown()
                    }
                    other => {
                        if let Type::Unknown(_) = other {
                            // Defer, but record that the receiver must be
                            // indexable so a closure like `(x) -> x[0]` rejects
                            // a non-indexable argument at its call site.
                            self.record_shape(&base_ty, ShapeConstraint::Indexable);
                        } else if !is_maybe_indexable(&other) {
                            self.errors.push(TypeError {
                                message: format!("cannot index `{}`", other.display()),
                                span: *span,
                            });
                        }
                        self.fresh_unknown()
                    }
                }
            }
            Expr::ErrorProp(inner, span) => {
                // `e!` unwraps a `Result`; the outer expectation W means the
                // inner must produce W!, so a keyed method inside `e` is keyed
                // by W -- keep the pending expectation for a direct inner call,
                // clear it otherwise so siblings do not see it.
                let ty = if matches!(&**inner, Expr::Call(..)) {
                    self.check_expr(inner, scopes)
                } else {
                    let saved = self.call_expected.take();
                    let t = self.check_expr(inner, scopes);
                    self.call_expected = saved;
                    t
                };
                let resolved = self.resolve(&ty);
                // `e!` on a NULLABLE operand unwraps the value; the null case
                // returns null itself from the enclosing callable, whose
                // return type therefore gains an outer `?`. The span is
                // recorded so MIR lowering emits the presence-test shape
                // instead of the `Result` tag-test shape.
                if let Type::Nullable(inner_ty) = &resolved {
                    self.check_null_propagation_return_context(*span);
                    self.record_prop_kind(*span, PropKind::Null);
                    self.null_props.insert(*span);
                    return (**inner_ty).clone();
                }
                match resolved.result_payloads() {
                    Some((ok, _)) => {
                        self.check_error_propagation_return_context(*span);
                        self.record_prop_kind(*span, PropKind::Err);
                        ok.clone()
                    }
                    None if resolved.is_result_type() => {
                        self.check_error_propagation_return_context(*span);
                        self.record_prop_kind(*span, PropKind::Err);
                        self.fresh_unknown()
                    }
                    None if resolved.is_unknown() => self.fresh_unknown(),
                    None => {
                        self.errors.push(TypeError {
                            message: format!(
                                "error propagation requires `Result` or a nullable, found `{}`",
                                resolved.display()
                            ),
                            span: inner.span(),
                        });
                        self.fresh_unknown()
                    }
                }
            }
            Expr::Closure(params, body, _) => {
                self.report_duplicate_params("closure", params);
                let mut inferred_env = env_from_scopes(scopes);
                let closure_scope = self.param_scope(params);
                inferred_env.extend(closure_scope.clone());
                let mut propagated = LightProps::default();
                self.infer_expr_light(body, &inferred_env, &mut propagated);
                let mut closure_scopes = scopes.clone();
                closure_scopes.push(closure_scope);
                self.const_scopes.push(HashSet::new());
                self.return_contexts.push(ReturnContext::Inferred);
                self.return_values.push(Vec::new());
                let body_val = self.check_expr(body, &mut closure_scopes);
                let collected = self.return_values.pop().unwrap_or_default();
                self.return_contexts.pop();
                self.const_scopes.pop();
                // A BLOCK body yields only what it `return`s (void without one),
                // matching the back ends -- its trailing expression is not the
                // value. Any other body form is a single expression whose value
                // is the implicit return. (Previously inverted on both counts:
                // the trailing expression typed a block closure's result and an
                // explicit `return` typed it void.)
                let ret = if matches!(&**body, Expr::Block(..)) {
                    self.reconcile_return_types(&collected, false)
                        .unwrap_or(Type::Void)
                } else {
                    body_val
                };
                let ret = self.wrap_inferred_fallible_return(ret, &propagated);
                // Reuse the parameter types from the scope the body was checked
                // against, so an unannotated parameter's inference variable is
                // shared between the `Fun` parameter and the return type. This
                // keeps the relationship between input and output (e.g. the
                // identity closure `(x) -> x` has type `(U) -> U` for the same
                // `U`), which `apply_callable` then instantiates per call site.
                // Without this the parameter would get a brand-new unknown,
                // letting `let s: string = ((x) -> x)(1)` type-check unsoundly.
                let frame = closure_scopes.last().expect("closure scope frame");
                let param_types = params
                    .iter()
                    .map(|p| {
                        frame
                            .get(&p.name)
                            .cloned()
                            .unwrap_or_else(|| self.fresh_unknown())
                    })
                    .collect();
                Type::Fun(param_types, Box::new(ret))
            }
            Expr::Array(es, _) => {
                // Consumed before the elements are checked, so only the direct
                // initializer of an unannotated `const` binding is fixed-length;
                // nested literals and every other position stay slices.
                let fixed = std::mem::take(&mut self.fixed_array_binding);
                let elem_tys: Vec<Type> = es.iter().map(|e| self.check_expr(e, scopes)).collect();
                // Heterogeneous concrete elements form a tuple; otherwise an
                // array. A `null` element never forces a tuple: null unifies
                // with any element type, making the element nullable
                // (`[4, null, 65]` is an `int32?` sequence).
                if let Some(tuple) = self.tuple_of_elements(es, &elem_tys) {
                    Type::Tuple(tuple)
                } else {
                    let base = elem_tys
                        .iter()
                        .zip(es)
                        .find(|(_, e)| !matches!(e, Expr::Null(_)))
                        .map(|(t, _)| t.clone())
                        .unwrap_or_else(|| self.fresh_empty_array_elem());
                    let saw_null = es.iter().any(|e| matches!(e, Expr::Null(_)));
                    let elem_ty = if saw_null && !matches!(self.resolve(&base), Type::Nullable(_)) {
                        Type::Nullable(Box::new(base))
                    } else {
                        base
                    };
                    for (got, e) in elem_tys.iter().zip(es) {
                        if matches!(e, Expr::Null(_)) {
                            continue;
                        }
                        self.expect_expr_assignable(got, &elem_ty, e);
                    }
                    if fixed {
                        Type::Array(Box::new(elem_ty), es.len())
                    } else {
                        Type::Slice(Box::new(elem_ty))
                    }
                }
            }
            Expr::Range(lo, hi, _) => {
                // `[lo..hi]` -- both bounds are integers; the element type is
                // their common type, like a binary operator's operands.
                let lo_ty = self.check_expr(lo, scopes);
                let hi_ty = self.check_expr(hi, scopes);
                self.expect_int_index(&lo_ty, lo.span());
                self.expect_int_index(&hi_ty, hi.span());
                let elem = self.range_element_type(&lo_ty, lo, &hi_ty, hi);
                Type::Slice(Box::new(elem))
            }
            Expr::TypeLit(name, fields, span) => self.check_record_lit(name, fields, *span, scopes),
            Expr::VariantLit(t, variant, fields, span) => {
                self.check_variant_lit(t, variant, fields, *span, scopes)
            }
            Expr::If(cond, then, els, span) => {
                let cond_ty = self.check_condition(cond, scopes);
                let mut truth = cond_ty.static_truthiness();
                // Structural graceful degradation (the goal's structure-type rules):
                // when the condition is a field access whose then-branch does not
                // type for this concrete value (a present field whose type the
                // branch's `return` cannot produce; a missing field is already
                // `never?` and statically false above), the `if` folds to
                // statically false rather than a type error. The fold must mirror
                // the back end EXACTLY: the back end prunes an arm only when its
                // unconditionally-reached `return` value kind-conflicts with the
                // function's return type (`then_return_conflicts` in the engine).
                // Folding on any other branch error would discard diagnostics for
                // an arm the back end still emits and executes -- a type-check
                // bypass straight into the unboxed code.
                if truth != Some(false) && matches!(&**cond, Expr::Field(..)) {
                    let mark = self.errors.len();
                    let mut probe = scopes.clone();
                    self.apply_truthy_narrowing(cond, &mut probe);
                    // Isolate the probe's collected returns: they describe the
                    // (possibly dead) arm, not the enclosing callable, and the
                    // real walk below re-collects the live ones.
                    self.return_values.push(Vec::new());
                    self.check_branch(then, &mut probe, false);
                    let probe_returns = self.return_values.pop().unwrap_or_default();
                    let failed = self.errors.len() > mark;
                    self.errors.truncate(mark);
                    if failed && self.then_branch_return_conflicts(then, &probe_returns) {
                        truth = Some(false);
                    }
                }
                let mut then_scopes = scopes.clone();
                self.apply_truthy_narrowing(cond, &mut then_scopes);
                // A statically-known condition makes one arm unreachable. Its
                // body is still walked (so nested call instances are recorded for
                // monomorphization) but its type errors are discarded: a dead
                // path may not type-check -- e.g. a bare `null` (`never?`) whose
                // truthy arm narrows it to `never` -- yet must not reject the
                // program. The reachable arm alone determines the `if` type.
                let then_ty = self.check_branch(then, &mut then_scopes, truth == Some(false));
                let else_ty = match els {
                    Some(e) => self.check_branch_expr(e, scopes, truth == Some(true)),
                    None => Type::Void,
                };
                // A statically-folded `if` whose selected arm always returns
                // leaves the REST OF THE BLOCK unreachable (see
                // `Checker::static_divergence`). Only the selected arm counts: an
                // unselected arm's `return` is code the back end never emits.
                self.static_divergence = match truth {
                    Some(true) => block_always_returns(then),
                    Some(false) => els.as_deref().is_some_and(expr_always_returns),
                    None => false,
                };
                match truth {
                    Some(true) => then_ty,
                    Some(false) => else_ty,
                    None => self.common_type_or_error("if", then_ty, else_ty, *span),
                }
            }
            Expr::IfLet(pat, scrut, then, els, span) => {
                let scrut_ty = self.check_expr(scrut, scopes);
                self.check_pattern_against(&scrut_ty, pat);
                let mut then_scopes = scopes.clone();
                then_scopes.push(HashMap::new());
                self.const_scopes.push(HashSet::new());
                // A plain binding on a nullable scrutinee is a presence test, so on
                // the then-arm the value is proven non-null: bind it at the unwrapped
                // type (e.g. `if let p = T.from(v)` gives `p: T`), so `p.field` is
                // valid rather than a nullable-use error.
                let bind_ty = match (pat, &self.resolve(&scrut_ty)) {
                    (Pattern::Binding(_, _), Type::Nullable(inner)) => (**inner).clone(),
                    _ => scrut_ty.clone(),
                };
                self.bind_pattern(pat, &bind_ty, &mut then_scopes);
                let then_ty = self.check_block_expr(then, &mut then_scopes);
                self.const_scopes.pop();
                let else_ty = els
                    .as_ref()
                    .map(|e| self.check_expr(e, scopes))
                    .unwrap_or(Type::Void);
                self.common_type_or_error("if-let", then_ty, else_ty, *span)
            }
            Expr::Match(scrut, arms, span) => {
                let scrut_ty = self.check_expr(scrut, scopes);
                let mut result_ty: Option<Type> = None;
                for arm in arms {
                    self.check_pattern_against(&scrut_ty, &arm.pattern);
                    let mut arm_scopes = scopes.clone();
                    arm_scopes.push(HashMap::new());
                    self.const_scopes.push(HashSet::new());
                    self.bind_pattern(&arm.pattern, &scrut_ty, &mut arm_scopes);
                    let arm_ty = self.check_expr(&arm.body, &mut arm_scopes);
                    self.const_scopes.pop();
                    if let Some(prev) = &result_ty {
                        result_ty =
                            Some(self.common_type_or_error("match", prev.clone(), arm_ty, *span));
                    } else {
                        result_ty = Some(arm_ty);
                    }
                }
                result_ty.unwrap_or(Type::Void)
            }
            Expr::Block(b, _) => self.check_block_expr(b, scopes),
        }
    }

    pub(super) fn common_type_or_unknown(&mut self, left: Type, right: Type) -> Type {
        if let Some(nullable) = common_nullable_type(&left, &right) {
            return nullable;
        }
        if self.can_unify(&left, &right)
            || crate::structural::types_compatible(self.program, &left, &right)
        {
            left
        } else {
            self.fresh_unknown()
        }
    }

    fn common_type_or_error(
        &mut self,
        context: &str,
        left: Type,
        right: Type,
        span: prepoly_parser::Span,
    ) -> Type {
        // A diverged branch (`Never` -- it always returns or propagates, e.g.
        // a bare `null!`) constrains nothing; the other branch's type wins.
        match (self.resolve(&left), self.resolve(&right)) {
            (Type::Never, _) => return right,
            (_, Type::Never) => return left,
            _ => {}
        }
        if let Some(nullable) = common_nullable_type(&left, &right) {
            return nullable;
        }
        if self.can_unify(&left, &right)
            || crate::structural::types_compatible(self.program, &left, &right)
        {
            return left;
        }
        if !matches!(left, Type::Unknown(_)) && !matches!(right, Type::Unknown(_)) {
            self.errors.push(TypeError {
                message: format!(
                    "`{context}` branches have incompatible types `{}` and `{}`",
                    left.display(),
                    right.display()
                ),
                span,
            });
        }
        self.fresh_unknown()
    }

    /// Type an `if` block arm, discarding its errors when `dead` (statically
    /// unreachable). The arm is still walked so its nested call instances reach
    /// monomorphization; only the type errors -- which a dead path is allowed to
    /// have -- are rolled back.
    fn check_branch(&mut self, b: &Block, scopes: &mut ScopeStack, dead: bool) -> Type {
        let mark = self.errors.len();
        let ty = self.check_block_expr(b, scopes);
        if dead {
            self.errors.truncate(mark);
        }
        ty
    }

    /// As `check_branch`, for an `else` arm (a nested expression rather than a
    /// block; an `else if` chain or a braced block lowered to an expression).
    fn check_branch_expr(&mut self, e: &Expr, scopes: &mut ScopeStack, dead: bool) -> Type {
        let mark = self.errors.len();
        let ty = self.check_expr(e, scopes);
        if dead {
            self.errors.truncate(mark);
        }
        ty
    }

    /// AST mirror of the back end's `then_return_conflicts` (engine `mono`): the
    /// then-branch reaches a `return <value>` through straight-line statements
    /// only (any branching construct becomes a MIR `CondBranch`, which the back
    /// end does not fold through), and the returned value's primitive kind
    /// clearly conflicts with the enclosing declared return type (its Ok payload
    /// for a fallible signature). Only such arms are pruned by the back end, so
    /// only such arms may the checker fold; anything looser would tolerate an
    /// arm that still executes.
    fn then_branch_return_conflicts(
        &mut self,
        then: &Block,
        probe_returns: &[(Type, prepoly_parser::Span)],
    ) -> bool {
        let Some(ReturnContext::Explicit(want)) = self.return_contexts.last().cloned() else {
            return false;
        };
        let resolved_want = self.resolve(&want);
        let target = match resolved_want.result_payloads() {
            Some((ok, _)) => ok.clone(),
            None => resolved_want,
        };
        let mut ret_span = None;
        for stmt in &then.stmts {
            match stmt {
                Stmt::Return(Some(value), span) => {
                    if expr_may_branch(value) {
                        return false;
                    }
                    ret_span = Some(*span);
                    break;
                }
                Stmt::Return(None, _) => return false,
                s if stmt_may_branch(s) => return false,
                _ => {}
            }
        }
        let Some(span) = ret_span else {
            return false;
        };
        let Some((ty, _)) = probe_returns.iter().find(|(_, s)| *s == span) else {
            return false;
        };
        let ty = self.resolve(ty);
        // A returned `Result` flows whole rather than as the Ok payload; the
        // back end never folds on it.
        if ty.is_result_type() {
            return false;
        }
        prepoly_hir::primitive_kind_conflict(&ty, &target)
    }

    /// The type of a block in expression position: its trailing expression's, or
    /// `void` when it ends in a statement.
    ///
    /// A block that LEAVES -- through `return`, `break`, or `continue`, or through
    /// a trailing expression that itself diverges -- produces no value at all, so
    /// its type is `Never` rather than `void`. `Never` is absorbed by a branch join
    /// (see `common_type_or_error`), which is what lets one arm bail out without
    /// constraining the others:
    ///
    /// ```text
    /// let v = match r {
    ///     Ok { value } => value,          // int32
    ///     Err { error } => { return -1 }  // Never, not void
    /// }
    /// ```
    ///
    /// Typing that arm `void` made the join report `int32` and `void` as
    /// incompatible. Divergence anywhere in the block counts, not just in its last
    /// statement: whatever follows a `return` is unreachable, so the block still
    /// yields nothing. (The HM checker's `infer_block_value` has always done this
    /// for a trailing `return`; the two now agree.)
    fn check_block_expr(&mut self, b: &Block, scopes: &mut ScopeStack) -> Type {
        scopes.push(HashMap::new());
        self.const_scopes.push(HashSet::new());
        let mut last = Type::Void;
        let mut diverges = false;
        for s in &b.stmts {
            match s {
                Stmt::Expr(e) => {
                    last = self.check_expr(e, scopes);
                    diverges |= matches!(self.resolve(&last), Type::Never);
                }
                Stmt::Return(..) | Stmt::Break(_) | Stmt::Continue(_) => {
                    self.check_stmt(s, scopes);
                    last = Type::Void;
                    diverges = true;
                }
                _ => {
                    self.check_stmt(s, scopes);
                    last = Type::Void;
                }
            }
        }
        self.const_scopes.pop();
        scopes.pop();
        if diverges { Type::Never } else { last }
    }

    pub(super) fn check_place(&mut self, e: &Expr, scopes: &mut ScopeStack) -> Type {
        let ty = match e {
            Expr::Field(base, name, span) => self.check_field(base, name, *span, scopes),
            Expr::Index(base, idx, span) => {
                let base_ty = self.check_expr(base, scopes);
                let idx_ty = self.check_expr(idx, scopes);
                self.expect_int_index(&idx_ty, idx.span());
                let resolved = self.resolve(&base_ty);
                if let Some(elem) = prepoly_hir::index_element(&resolved) {
                    return elem;
                }
                match prepoly_hir::peel_modes(&resolved).clone() {
                    // A store into an open array variable pins its element type,
                    // the way `push` pins it on the read side: `self.entries[i] =
                    // v` ties the field's still-open element to `v`'s type while
                    // checking. Only fires when the base is genuinely open -- a
                    // concrete `Slice`/`Array` is handled by `index_element` above,
                    // so a real element-type clash at a store still surfaces.
                    open @ Type::Unknown(_) => {
                        let elem = self.fresh_unknown();
                        let _ = self
                            .solver
                            .unify(&open, &Type::Slice(Box::new(elem.clone())));
                        elem
                    }
                    Type::Nullable(_) => {
                        self.report_nullable_use(*span);
                        self.fresh_unknown()
                    }
                    // A string is immutable and not element-addressable storage;
                    // it is indexable in read position, but never a valid store
                    // target (the unboxed back end has no cell to write).
                    Type::Str => {
                        self.errors.push(TypeError {
                            message: "cannot assign through a string index; strings are immutable"
                                .to_string(),
                            span: *span,
                        });
                        self.fresh_unknown()
                    }
                    other => {
                        if !is_maybe_indexable(&other) {
                            self.errors.push(TypeError {
                                message: format!("cannot index `{}`", other.display()),
                                span: *span,
                            });
                        }
                        self.fresh_unknown()
                    }
                }
            }
            // A place must be assignable: a variable, `self`, or a projection of
            // one. Anything else (a literal, call result, etc.) is not a valid
            // assignment target.
            Expr::Ident(..) | Expr::SelfExpr(_) => return self.check_expr(e, scopes),
            other => {
                self.errors.push(TypeError {
                    message: "invalid assignment target".to_string(),
                    span: other.span(),
                });
                return self.check_expr(e, scopes);
            }
        };
        self.record_expr_type(e, &ty);
        ty
    }

    /// Type a condition and return its resolved type. A condition may be of any
    /// type; its runtime truthiness is derived from the type rather than
    /// restricting what is accepted: a `bool` is used directly, a nullable tests
    /// non-null (and narrows on the truthy arm), and any other (non-nullable)
    /// type is unconditionally true. The resolved type lets callers fold a
    /// statically-known condition (see `static_truthiness`).
    pub(super) fn check_condition(&mut self, cond: &Expr, scopes: &mut ScopeStack) -> Type {
        let ty = self.check_expr(cond, scopes);
        self.resolve(&ty)
    }

    /// The element type bound by a `for` loop over `iter_ty`, seeing through
    /// reference/mutability wrappers and re-applying them to the element (over a
    /// `ref(mut(T[]))` each element is a `ref(mut(T))`). An as-yet-unconstrained
    /// iterand (possibly under wrappers) is constrained to a slice. `None` when the
    /// iterand is not a sequence.
    pub(super) fn for_element(&mut self, iter_ty: &Type) -> Option<Type> {
        match self.resolve(iter_ty) {
            Type::Slice(e) | Type::Array(e, _) => Some(*e),
            Type::Ref(inner) => self.for_element(&inner).map(|e| Type::Ref(Box::new(e))),
            Type::Mut(inner) => self.for_element(&inner).map(|e| Type::Mut(Box::new(e))),
            Type::ConstOf(inner) => self.for_element(&inner).map(|e| Type::ConstOf(Box::new(e))),
            resolved @ Type::Unknown(_) => {
                let elem = self.fresh_unknown();
                let _ = self
                    .solver
                    .unify(&resolved, &Type::Slice(Box::new(elem.clone())));
                Some(elem)
            }
            _ => None,
        }
    }

    /// The element type of `[lo..hi]`: the bounds' common integer type -- the
    /// smallest both flow into, exactly as a binary operator types its
    /// operands. Forcing `hi` into `lo`'s type would make the LITERAL's
    /// default width dominate (`[0..a.len()]` would demand int64 -> int32
    /// narrowing); instead a literal bound adapts to the other bound when its
    /// value fits, so counting over a length runs at the length's width.
    fn range_element_type(&mut self, lo_ty: &Type, lo: &Expr, hi_ty: &Type, hi: &Expr) -> Type {
        let lo_r = self.resolve(lo_ty);
        let hi_r = self.resolve(hi_ty);
        match (&lo_r, &hi_r) {
            // An open bound (still being inferred) follows the other side.
            (Type::Unknown(_), _) => hi_r,
            (_, Type::Unknown(_)) => lo_r,
            (Type::Int(_), Type::Int(_)) => {
                if integer_literal_fits(lo, &hi_r) {
                    return hi_r;
                }
                if integer_literal_fits(hi, &lo_r) {
                    return lo_r;
                }
                if let Some(t) = common_numeric_type(&lo_r, &hi_r) {
                    return t;
                }
                // No value-preserving common width (e.g. int64 with uint64):
                // report on `hi` with the explicit-conversion hint.
                self.expect_expr_assignable(&hi_r, &lo_r, hi);
                lo_r
            }
            // A non-integer bound was already rejected by expect_int_index;
            // keep the integer side for downstream typing.
            (Type::Int(_), _) => lo_r,
            _ => hi_r,
        }
    }

    fn expect_int_index(&mut self, ty: &Type, span: prepoly_parser::Span) {
        match self.resolve(ty) {
            Type::Int(_) | Type::Unknown(_) => {}
            other => self.errors.push(TypeError {
                message: format!("index must be an integer, found `{}`", other.display()),
                span,
            }),
        }
    }

    /// If a bracket literal's elements describe a tuple, return their types; else
    /// `None` (an array). Mirrors `hm::tuple_of_elements`: a rolled-back probe over
    /// each element's representative type (a numeric literal stands in as its
    /// default kind, not its open variable) decides array-vs-tuple, and a tuple
    /// returns the elements' actual types so an annotation can still fix widths.
    pub(super) fn tuple_of_elements(
        &mut self,
        elems: &[Expr],
        elem_tys: &[Type],
    ) -> Option<Vec<Type>> {
        if elems.len() < 2 {
            return None;
        }
        // Null elements are excluded from the probe: a null unifies with any
        // element type (the sequence's element just becomes nullable), so only
        // the non-null elements decide array-vs-tuple.
        let reps: Vec<Type> = elems
            .iter()
            .zip(elem_tys)
            .filter(|(e, _)| !matches!(e, Expr::Null(_)))
            .map(|(e, t)| numeric_literal_repr(e).unwrap_or_else(|| self.resolve(t)))
            .collect();
        let (first, rest) = reps.split_first()?;
        // Two DISTINCT unresolved variables would "unify" -- but only by coupling
        // two values nothing says are related. An array's elements must all be the
        // same type; independent unknowns are not known to be, so the literal is a
        // tuple and each position keeps its own type. This is what `[e.key,
        // e.value]` inside `HashMap.pairs` needs: its two halves are the map's
        // separate key and value slots, and typing them as one array element made
        // the method's scheme return `key[]` -- so `for [k, v] in m.pairs()` saw
        // both halves as the key's type.
        let distinct_unknowns = reps.iter().all(|t| matches!(t, Type::Unknown(_)))
            && reps
                .iter()
                .enumerate()
                .any(|(i, t)| reps.iter().skip(i + 1).any(|u| t != u));
        if distinct_unknowns {
            return Some(elem_tys.iter().map(|t| self.resolve(t)).collect());
        }
        let snap = self.solver.snapshot();
        let unifiable = rest.iter().all(|t| self.solver.unify(first, t).is_ok());
        self.solver.rollback(snap);
        if unifiable {
            None
        } else {
            Some(elem_tys.iter().map(|t| self.resolve(t)).collect())
        }
    }
}
