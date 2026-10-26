//! Expression typing below the `check_expr` hub: the per-node dispatcher
//! (`check_expr_inner`), checking against a requirement (literals,
//! constructions, closures and branch values that adapt to their slot),
//! closure bodies and their results, `!` propagation, `if`/`if let`/`match`/
//! block values with the static folds of presence tests and type tests and
//! the join of the live branches, places, conditions, and the element types
//! of ranges, bracket literals and `for` iterands.

use super::*;

impl<'a> Checker<'a> {
    /// [`Self::check_expr_against_at`] for a storage site.
    pub(super) fn check_expr_against(
        &mut self,
        expr: &Expr,
        want: &Type,
        scopes: &mut ScopeStack,
    ) -> Type {
        self.check_expr_against_at(expr, want, FlowSite::Storage, scopes)
    }

    /// Check `expr` in a position that requires `want`, flowing at a site of
    /// kind `site`, and return the value's own type. The requirement directs
    /// the check where a construction adapts to its slot: an integer literal
    /// takes the required width, array/tuple literal elements and closure
    /// parameters take the required element/parameter types, a record
    /// literal is built at the required record's instance (an anonymous one
    /// only when its fields are exactly the record's, see
    /// [`Self::check_anonymous_literal_against`]), and an `if`/`match`/block
    /// hands the requirement to its branch values. Elements and closure
    /// results nested in such a construction are storage whatever `site` is.
    pub(super) fn check_expr_against_at(
        &mut self,
        expr: &Expr,
        want: &Type,
        site: FlowSite,
        scopes: &mut ScopeStack,
    ) -> Type {
        // A narrowed binding handed to a `ref(mut(T?))` parameter is passed as
        // the binding itself, at its declared nullable type.
        if let Some(declared) = self.narrowed_ref_mut_argument(expr, want, scopes) {
            self.record_expr_type(expr, &declared);
            self.expect_expr_assignable_at(&declared, want, expr, site);
            return declared;
        }
        // An integer literal in a numeric required position takes that type
        // when its value fits (an integer range holding it, or a float that
        // represents it exactly): record it at the target type so its runtime
        // representation matches the position rather than its default type.
        if let Some(v) = expr.int_literal_value() {
            let target = match self.resolve(want) {
                Type::Nullable(inner) => *inner,
                other => other,
            };
            if matches!(target, Type::Int(_) | Type::Float(_))
                && brass_typesys::literal_fits(v, &target)
            {
                self.record_expr_type(expr, &target);
                return target;
            }
        }
        // A bracket literal takes the requirement's shape; under a nullable
        // requirement (`[int32, int32]?`) the literal is the present value.
        let bracket_want = match self.resolve(want) {
            Type::Nullable(inner) if matches!(expr, Expr::Array(..)) => self.resolve(&inner),
            other => other,
        };
        if let (Expr::Array(items, span), Type::Array(elem, len)) = (expr, bracket_want.clone()) {
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
                self.check_element_value(item, &elem, scopes);
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
        if let (Expr::Array(items, _), Type::Slice(elem)) = (expr, bracket_want.clone()) {
            for item in items {
                self.check_expr_against(item, &elem, scopes);
            }
            let ty = Type::Slice(elem);
            self.record_expr_type(expr, &ty);
            return ty;
        }
        // A bracket literal in a required tuple position: each element flows into
        // its own expected type, so e.g. an int literal takes the annotated width.
        if let (Expr::Array(items, span), Type::Tuple(elems)) = (expr, bracket_want) {
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
            let instantiated = items
                .iter()
                .zip(&elems)
                .map(|(item, expected)| {
                    let actual = self.check_expr_against(item, expected, scopes);
                    self.instantiate_annotated_type(expected, &actual)
                })
                .collect();
            let ty = Type::Tuple(instantiated);
            self.record_expr_type(expr, &ty);
            return ty;
        }
        // A named record literal flowing into a slot of its own record type is
        // built at the slot's instance: a field the slot's refinement pins
        // (`let c: Box64 = Box { item: 4 }`) takes the pinned type, so a
        // literal value adapts to it.
        if let Expr::TypeLit(name, fields, span) = expr
            && !name.is_empty()
            && let Type::Record(slot) =
                brass_typesys::strip_nullable(peel_modes(&self.resolve(want)).clone())
            && self.record_head_id(name) == Some(slot.id)
        {
            let ty = self.check_record_lit(name, fields, *span, Some(&slot.substitution), scopes);
            self.record_expr_type(expr, &ty);
            self.expect_expr_assignable_at(&ty, want, expr, site);
            return ty;
        }
        if let Expr::TypeLit(name, fields, _) = expr
            && name.is_empty()
            && let Some(target) = self.anonymous_literal_target(want)
            && let Some(ty) =
                self.check_anonymous_literal_against(expr, fields, target, want, site, scopes)
        {
            return ty;
        }
        // A closure in a position that wants a function type is checked against
        // that type: each parameter takes the expected parameter type (so an
        // unannotated `self`/value parameter is typed without a separate
        // annotation) and the body is checked against the expected return, so a
        // block-bodied closure's `return` reconciles with it rather than leaving
        // the closure's result `void`.
        if let Expr::Closure(params, body, span) = expr
            && let Type::Fun(want_params, want_ret) = self.resolve(want)
        {
            let mut captured = self.closure_capture_scopes(scopes, *span);
            let got = self.check_closure_against(
                expr,
                params,
                body,
                (&want_params, Some(&want_ret)),
                &mut captured,
            );
            self.expect_expr_assignable(&got, want, expr);
            // The literal's own type (its parameters are the expected ones)
            // is what the back end instantiates the closure at.
            self.record_expr_type(expr, &got);
            return got;
        }
        // A branching expression hands the requirement to its branch values
        // (see `Checker::branch_expectation`): an anonymous record literal in
        // a branch is built as the slot's record, a bracket literal takes its
        // shape and a closure its parameter types, exactly as for a direct
        // initializer; under a numeric requirement the branches written as
        // literals adapt to it (see `Checker::join_branch_types`).
        let mut delegated = false;
        if matches!(
            expr,
            Expr::If(..) | Expr::IfLet(..) | Expr::Match(..) | Expr::Block(..)
        ) {
            let resolved = self.resolve(want);
            delegated = brass_typesys::shapes_constructions(&resolved);
            if delegated || numeric_requirement(&resolved).is_some() {
                self.branch_expectation = Some((want.clone(), site));
            }
        }
        let taken_before = std::mem::replace(&mut self.branch_expectation_taken, false);
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
        self.branch_expectation = None;
        // Branch values that were each checked against a construction
        // requirement already flowed into it: checking their join again would
        // only restate a branch's error at the whole expression.
        let delegated = delegated && self.branch_expectation_taken;
        self.branch_expectation_taken = taken_before;
        // A function named as a value with optional trailing parameters
        // takes the arity of the function type it is checked against.
        self.expect_function_value(&got, want, expr.span());
        // A still-open value in a required FUNCTION position takes that type
        // outright. The assignability check below only PROBES and commits
        // nothing, so without this `fun g(handler) { f(handler) }` -- with
        // `f`'s parameter annotated `(int32) -> void` -- would leave `g`'s
        // parameter an open variable (`handler: unknown_0` on every editor
        // surface). The annotation is the whole call contract of a function
        // value, so binding to it is inference, not a guess. Function
        // positions ONLY: a record position must stay open for structural
        // width, and a numeric one converts rather than unifies.
        if matches!(self.resolve(want), Type::Fun(..)) {
            let resolved_got = self.resolve(&got);
            if !brass_hir::is_fully_known(&resolved_got) && self.can_unify(&got, want) {
                let _ = self.solver.unify(&got, want);
            }
        }
        if !delegated {
            self.expect_expr_assignable_at(&got, want, expr, site);
        }
        got
    }

    /// The requirement handed to the `if`/`match`/block expression being
    /// checked (see `Checker::branch_expectation`), marking it as passed on to
    /// the branch values.
    fn take_branch_expectation(&mut self) -> Option<(Type, FlowSite)> {
        let expect = self.branch_expectation.take();
        self.branch_expectation_taken |= expect.is_some();
        expect
    }

    fn check_error_propagation_return_context(&mut self, operand: &Type, span: brass_parser::Span) {
        match self.return_contexts.last() {
            Some(ReturnContext::Inferred) => {}
            Some(ReturnContext::Explicit(ret)) if is_result_return_type(&self.resolve(ret)) => {
                // The failure arm returns the operand's Result unchanged, so
                // the operand's declaration must be the one the callable
                // returns: a scope's shadowing `Result` and the prelude's are
                // distinct nominals even though both satisfy the sugar shape.
                let resolved_ret = self.resolve(ret);
                let ret_result = match &resolved_ret {
                    Type::Nullable(inner) => inner.as_ref(),
                    other => other,
                };
                if let (Type::Sum(have), Type::Sum(want)) = (operand, ret_result)
                    && have.is_result_type()
                    && want.is_result_type()
                    && have.id != want.id
                {
                    self.errors.push(TypeError {
                        message: format!(
                            "`!` propagates its operand's `Result` declaration unchanged, \
                             but the operand and the return type resolve to different \
                             `Result` declarations (`{}` vs `{}`)",
                            operand.display(),
                            resolved_ret.display()
                        ),
                        span,
                    });
                }
            }
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

    /// Join the error payload a Result-operand `!` at `span` propagates with
    /// the Err payload of the enclosing callable's DECLARED Result return.
    ///
    /// The failure arm returns the operand's error (lifted into the prelude
    /// `Error`) from the callable, so it is one of the callable's error
    /// sources, and all of them must join to one payload type (types.md,
    /// Result) -- exactly as the `error(..)` returns checked against the same
    /// annotation must. A `T!` names only the Ok side: its still-open Err is
    /// bound here when this `!` is the first source the walk meets, the way a
    /// forwarded `return` binds it (see `link_forwarded_error`). Inferred
    /// return contexts reconcile their sources in the light assembly instead,
    /// and the entry `main` and module top level abort rather than return.
    fn join_propagated_error(&mut self, err: &Type, span: brass_parser::Span) {
        if err.is_unknown() || self.in_entry_main && self.return_contexts.len() == 1 {
            return;
        }
        let Some(ReturnContext::Explicit(ret)) = self.return_contexts.last() else {
            return;
        };
        let declared = match self.resolve(ret) {
            Type::Nullable(inner) => *inner,
            other => other,
        };
        let Some((_, want_err)) = declared.result_payloads() else {
            return;
        };
        let want_err = want_err.clone();
        let lifted = crate::lift_err_payload(self.program, err.clone());
        if self.resolve(&want_err).is_unknown() {
            let _ = self.solver.unify(&want_err, &lifted);
            return;
        }
        self.join_declared_error(&want_err, &lifted, "this `!` propagates", span);
    }

    /// Whether the error payload `raised` (an error source of the enclosing
    /// callable: a `!`'s lifted operand payload, a returned `Result`'s Err)
    /// joins with the callable's declared Err payload `declared`. A conflict
    /// is reported at `span` as incompatible error payloads, naming what the
    /// source does (`doing`), and `false` is returned.
    pub(super) fn join_declared_error(
        &mut self,
        declared: &Type,
        raised: &Type,
        doing: &str,
        span: brass_parser::Span,
    ) -> bool {
        // The declared payload comes first, so a conflict is reported at the
        // source (the second operand).
        let sources = [(declared.clone(), span), (raised.clone(), span)];
        // The payloads must have a value join (two instances of the prelude
        // `Error` join on their shared slots); anything else is a conflict.
        let joins = match self.join_known_values(&sources) {
            Some(joined) => joined.is_ok(),
            // A payload with open parts: the join decides only between known
            // types, so fall back to the unifiability the open walk uses.
            None => self.can_unify(declared, raised),
        };
        if joins {
            return true;
        }
        let declared = self.resolve(declared);
        let raised = self.resolve(raised);
        self.errors.push(TypeError {
            message: format!(
                "incompatible error payloads: `{}` and `{}`: {doing} `{}`, but the \
                 enclosing function's Result carries `{}`",
                declared.display(),
                raised.display(),
                raised.display(),
                declared.display()
            ),
            span,
        });
        false
    }

    /// `e!` on a NULLABLE operand returns null from the enclosing callable on
    /// the null case, so that callable's return must be able to be null: an
    /// inferred return (it gains an outer `?`), a nullable annotation, or a
    /// void one (statement use -- the null carries no observable value). The
    /// entry `main`'s own body and the module top level abort at runtime
    /// instead, so they need no such return type.
    fn check_null_propagation_return_context(&mut self, span: brass_parser::Span) {
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
    pub(super) fn record_prop_kind(&mut self, span: brass_parser::Span, kind: PropKind) {
        self.journal_elaboration(ElaborationJournalEntry::PropKind(span, kind));
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

    /// Record whether the `!` (or forwarded return) at `span` re-wraps a raw
    /// error payload into the prelude `Error`, and reject a generic whose
    /// instantiations disagree. `lift_errs` is a span SET consumed by ONE
    /// shared MIR lowering: unioned across instantiations, the lift arm would
    /// double-wrap an already-`Error` payload of the instance that must not
    /// lift (or drop the wrap of the one that must). Only called once the
    /// payload type is resolved, so the template elaboration stays silent.
    pub(super) fn record_lift_kind(&mut self, span: brass_parser::Span, lifted: bool) {
        self.journal_elaboration(ElaborationJournalEntry::LiftKind(span, lifted));
        if self.lift_poisoned.contains(&span) {
            return;
        }
        match self.lift_kinds.get(&span) {
            None => {
                self.lift_kinds.insert(span, lifted);
            }
            Some(prev) if *prev != lifted => {
                self.errors.push(TypeError {
                    message: "`!` re-wraps a raw error payload into `Error` in one \
                              instantiation of this generic function and propagates an \
                              already-wrapped `Error` in another; the two lower \
                              differently, so the error payload must resolve to one \
                              kind in every instantiation (annotate the parameter to \
                              fix it)"
                        .to_string(),
                    span,
                });
                self.lift_poisoned.insert(span);
            }
            _ => {}
        }
    }

    /// What a closure body returns, from its checked parts: the value of an
    /// expression body, or the join of a block body's `return`s (`void`
    /// without one), with the `Result` layer its error sites add and the
    /// nullable layer its null-propagating `!`s add.
    ///
    /// A BLOCK body yields only what it `return`s, matching the back ends --
    /// its trailing expression is not the value. A `return error(..)` -- a
    /// Result whose Ok payload is still open -- is an ERROR SITE, not an
    /// ordinary return: its Err payload joins the fallible layer and the bare
    /// returns alone reconcile as the Ok side, exactly how
    /// `infer_returns_block` classifies a named function's returns. A
    /// COMPLETE forwarded Result (known Ok payload) still flows whole. A `!`
    /// the light walk could not classify (a builtin container's `m.get(k)!`)
    /// is a null propagation once the full check resolved its operand to a
    /// nullable.
    pub(super) fn closure_body_result(
        &mut self,
        body: &Expr,
        body_val: Type,
        returned: Vec<(Type, brass_parser::Span)>,
        mut props: LightProps,
    ) -> Type {
        for span in own_error_props(body) {
            if self.prop_kinds.get(&span) == Some(&Some(PropKind::Null))
                && !props.nulls.contains(&span)
            {
                props.nulls.push(span);
            }
        }
        let normal: Vec<(Type, brass_parser::Span)> = returned
            .into_iter()
            .filter(|(t, span)| match self.resolve(t).result_payloads() {
                Some((ok, err)) if ok.is_unknown() => {
                    let lifted = crate::lift_err_payload(self.program, self.resolve(err));
                    props.errors.push((lifted, *span));
                    false
                }
                _ => true,
            })
            .collect();
        let ret = if matches!(body, Expr::Block(..)) {
            self.report_instance_return_conflict(&normal, !props.errors.is_empty());
            self.reconcile_return_types(&normal, false)
                .unwrap_or(Type::Void)
        } else {
            body_val
        };
        // An already-`Result` value (a pure thrower or forwarder) must not
        // gain a second Result layer from the sites that built it; the
        // null-propagation wrapper still applies.
        if self.resolve(&ret).is_result_type() {
            super::precompute::wrap_null_propagated_return(ret, &props.nulls)
        } else {
            self.wrap_inferred_fallible_return(ret, &props)
        }
    }

    fn wrap_inferred_fallible_return(&mut self, ok: Type, props: &LightProps) -> Type {
        let base = if props.errors.is_empty() {
            ok
        } else {
            let err = self
                .reconcile_error_payloads(&props.errors, true)
                .unwrap_or_else(|| self.fresh_unknown());
            let span = props
                .errors
                .first()
                .map(|(_, s)| *s)
                .unwrap_or(brass_parser::Span::new(0, 0));
            self.scoped_result(ok, err, span)
        };
        super::precompute::wrap_null_propagated_return(base, &props.nulls)
    }

    /// Type the expression `e`, dispatching on its kind. Reached through
    /// `check_expr`, which records the result for `e`'s span.
    pub(super) fn check_expr_inner(&mut self, e: &Expr, scopes: &mut ScopeStack) -> Type {
        match e {
            Expr::Int(v, _) => int_literal_type(*v),
            Expr::Float(_, _) => Type::Float(FloatKind::F64),
            Expr::Bool(_, _) => Type::Bool,
            Expr::Null(_) => Type::null(),
            Expr::Str(segs, _) => {
                for seg in segs {
                    if let StrSeg::Expr(e) = seg {
                        let ty = self.check_expr(e, scopes);
                        self.expect_renderable(&ty, e.span(), "cannot interpolate");
                        self.invalidate_after_rendering(&ty, scopes);
                    }
                }
                Type::Str
            }
            Expr::Ident(name, span) => {
                if let Some(t) = self.lookup(scopes, name) {
                    self.note_narrowed_use(scopes, name, *span);
                    self.reject_error_only_binding_read(name, &t, *span);
                    // Every body's bottom frame is the global scope.
                    if (self.co_checking || self.has_global_dependency_observer())
                        && scopes.iter().rposition(|scope| scope.contains_key(name)) == Some(0)
                    {
                        self.record_global_dependency(name, &t, false);
                        if self.co_checking {
                            self.record_co_global_read(name);
                        }
                    }
                    self.instantiate_closure_scheme(t)
                } else if let Some(t) = self.lookup_aliased_global(name) {
                    self.record_global_dependency(name, &t, true);
                    // A global reached under an import rename or a module
                    // qualifier; the global scope holds it under its declared name.
                    self.instantiate_closure_scheme(t)
                } else if self.is_resolvable_free_name(name) {
                    // A free function or runtime builtin used as a first-class
                    // value. A completely annotated signature IS its type; a
                    // generic function's type is recovered at the call site,
                    // so here the name is only accepted as resolved.
                    self.elaborate_keyed_function_value(name, *span);
                    self.function_value_type(name, *span)
                        .unwrap_or_else(|| self.fresh_unknown())
                } else if self
                    .global_defs
                    .get(&self.current_module)
                    .is_some_and(|own| own.contains_key(name))
                {
                    // A global of this module that top-level code reads before
                    // its declaration: the initialization-order check reports
                    // it ("used before it is initialized"), not as unknown.
                    let ty = self.fresh_unknown();
                    self.record_global_dependency(name, &ty, false);
                    ty
                } else {
                    // An undeclared value name. Name resolution is a hard
                    // pre-execution check, so this is an
                    // error rather than a fresh unknown that would launder into
                    // any required type and run as `void`. `infer` as a value is
                    // the reflective conversion `infer.from(x)`, which only a
                    // decoder template's specialization resolves.
                    let message = if name == "infer" {
                        "`infer.from(x)` is valid only inside a reflective decoder method \
                         (`fun T.m(self) -> infer!`), where `infer` is the target type"
                            .to_string()
                    } else {
                        format!("unknown name `{name}`")
                    };
                    self.errors.push(TypeError {
                        message,
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
            // A negated integer literal is one literal: its value (sign
            // included) decides its default type, so `-2147483648` is an
            // `int32` and a value below `INT64_MIN` is rejected here.
            Expr::Unary(_, _, span) if let Some(value) = e.int_literal_value() => {
                if brass_typesys::int_literal_kind(value).is_none() {
                    self.errors.push(TypeError {
                        message: "integer literal out of range: no integer type holds it"
                            .to_string(),
                        span: *span,
                    });
                }
                int_literal_type(value)
            }
            Expr::Unary(op, inner, span) => {
                let ty = if matches!(op, UnaryOp::Not) {
                    let ty = self.check_null_test_operand(inner, scopes);
                    // Testing a narrowed binding is always allowed: `!x` tests
                    // its declared nullable, whatever a narrowing proved here.
                    match &**inner {
                        Expr::Ident(name, _) => {
                            self.narrowed_declared_type(scopes, name).unwrap_or(ty)
                        }
                        _ => ty,
                    }
                } else {
                    self.check_expr(inner, scopes)
                };
                self.check_unary(*op, &ty, *span)
            }
            Expr::Binary(op, a, b, span) => {
                let (left, right) = if is_null_test(*op, a, b) {
                    (
                        self.check_null_test_operand(a, scopes),
                        self.check_null_test_operand(b, scopes),
                    )
                } else {
                    (self.check_expr(a, scopes), self.check_expr(b, scopes))
                };
                self.check_binary_expr(*op, a, &left, b, &right, *span)
            }
            Expr::Call(callee, args, span) => self.check_call(callee, args, *span, scopes),
            Expr::Field(base, name, span) => {
                let ty = self.check_field(base, name, *span, scopes);
                self.note_tested_field_read(e, &ty, scopes);
                ty
            }
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
                if let Some(elem) = brass_hir::index_element(&resolved) {
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
                    self.record_null_prop(*span);
                    return (**inner_ty).clone();
                }
                match resolved.result_payloads() {
                    Some((ok, err)) => {
                        let ok = ok.clone();
                        let err = self.resolve(err);
                        self.reject_error_only_unwrap(&ok, *span);
                        self.check_error_propagation_return_context(&resolved, *span);
                        self.join_propagated_error(&err, *span);
                        self.record_prop_kind(*span, PropKind::Err);
                        self.full_err_props
                            .insert(*span, crate::lift_err_payload(self.program, err.clone()));
                        self.record_sum_view_identity(inner.span());
                        // A propagated payload that is not the prelude Error
                        // is re-raised wrapped into one (gaining this site's
                        // location); MIR's propagation arm does the rebuild.
                        if !err.is_unknown() {
                            let lifted = crate::lift_err_payload(self.program, err.clone()) != err;
                            self.record_lift_kind(*span, lifted);
                            if lifted {
                                self.record_lift_err(*span);
                            }
                        }
                        ok
                    }
                    None if resolved.is_result_type() => {
                        self.check_error_propagation_return_context(&resolved, *span);
                        self.record_prop_kind(*span, PropKind::Err);
                        self.record_sum_view_identity(inner.span());
                        self.fresh_unknown()
                    }
                    None if resolved.is_unknown() => self.fresh_unknown(),
                    None => {
                        // A declared subtype of the scope's Result unwraps
                        // like a Result: the operand is coerced to the parent
                        // at its own span (the same rebuild a return-position
                        // flow gets) and `!` proceeds on the parent.
                        let scoped = {
                            let ok = self.fresh_unknown();
                            let err = self.fresh_unknown();
                            self.scoped_result(ok, err, *span)
                        };
                        if let (Type::Sum(h), Type::Sum(w)) = (&resolved, &scoped)
                            && h.id != w.id
                            && crate::structural::declares_sum_parent(self.program, h.id, w.id, 0)
                        {
                            self.record_sum_view(&resolved, &scoped, inner.span());
                            let coerced = self.resolve(&scoped);
                            let (ok, err) = coerced
                                .result_payloads()
                                .map(|(ok, err)| (ok.clone(), err.clone()))
                                .unwrap_or_else(|| (self.fresh_unknown(), self.fresh_unknown()));
                            // The rebuilt payload lifts exactly like a plain
                            // Result's (see above); without this the subtype's
                            // raw payload propagates and the arm returns the
                            // rebuilt Result whole, pinning the enclosing
                            // callable's Ok side to the SUBTYPE's Ok payload.
                            let err = self.resolve(&err);
                            // The light return walk needs this site's error
                            // evidence to retain the enclosing Result shape.
                            self.full_err_props
                                .insert(*span, crate::lift_err_payload(self.program, err.clone()));
                            if !err.is_unknown() {
                                let lifted =
                                    crate::lift_err_payload(self.program, err.clone()) != err;
                                self.record_lift_kind(*span, lifted);
                                if lifted {
                                    self.record_lift_err(*span);
                                }
                            }
                            self.check_error_propagation_return_context(&coerced, *span);
                            self.record_prop_kind(*span, PropKind::Err);
                            return ok;
                        }
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
            Expr::Closure(params, body, span) => {
                self.report_duplicate_params("closure", params);
                let closure_scope = self.param_scope(params);
                // Its still-open parameters are typed by each application;
                // an operation on one next to a literal follows it (see
                // `check_binary_expr`).
                for ty in closure_scope.values() {
                    if let Type::Unknown(id) = ty {
                        self.closure_param_vars.insert(*id);
                    }
                }
                let instance_params: Vec<_> = if self.numeric_enabled {
                    params
                        .iter()
                        .map(|p| {
                            closure_scope
                                .get(&p.name)
                                .cloned()
                                .unwrap_or_else(|| self.fresh_unknown())
                        })
                        .collect()
                } else {
                    Vec::new()
                };
                let captured = self.closure_capture_scopes(scopes, *span);
                let mut closure_scopes = captured.clone();
                closure_scopes.push(Scope::new(closure_scope));
                let mut propagated = LightProps::default();
                self.infer_expr_light(body, &closure_scopes, &mut propagated);
                self.const_scopes.push(HashSet::default());
                if self.numeric_enabled {
                    self.enter_closure_instance(params, body, &instance_params, &captured);
                }
                if self.numeric.probing {
                    self.enter_numeric_body(body.span());
                    self.numeric.returns.push(Vec::new());
                }
                self.return_contexts.push(ReturnContext::Inferred);
                self.return_values.push(Vec::new());
                // The body runs when the closure is called, not here: it is
                // not part of the enclosing path's narrowing flow.
                let body_val = self.with_detached_flow(|this| match &**body {
                    Expr::Block(block, _) => {
                        this.check_closure_block_body(body, block, &mut closure_scopes)
                    }
                    other => this.check_expr(other, &mut closure_scopes),
                });
                let collected = self.return_values.pop().unwrap_or_default();
                if self.numeric.probing {
                    self.numeric.returns.pop();
                    self.leave_numeric_body(true);
                }
                if self.numeric_enabled {
                    self.leave_instance();
                }
                self.return_contexts.pop();
                self.const_scopes.pop();
                let ret = self.closure_body_result(body, body_val, collected, propagated);
                // Reuse the parameter types from the scope the body was checked
                // against, so an unannotated parameter's inference variable is
                // shared between the `Fun` parameter and the return type. This
                // keeps the relationship between input and output (e.g. the
                // identity closure `(x) -> x` has type `(U) -> U` for the same
                // `U`): an application commits `U` to its argument
                // (`apply_callable`), and a generalized `let` binding gets a
                // fresh `U` per use (`instantiate_closure_scheme`). With a
                // brand-new unknown for the parameter,
                // `let s: string = ((x) -> x)(1)` would type-check unsoundly.
                let frame = closure_scopes.last().expect("closure scope frame");
                let param_types: Vec<_> = params
                    .iter()
                    .map(|p| {
                        if p.name == "_" {
                            p.ty.as_ref()
                                .and_then(|t| self.resolve_type(t).ok())
                                .unwrap_or_else(|| self.fresh_unknown())
                        } else {
                            frame
                                .get(&p.name)
                                .cloned()
                                .unwrap_or_else(|| self.fresh_unknown())
                        }
                    })
                    .collect();
                let (ret, identity) = self.inferred_closure_result(ret);
                self.remember_closure(e, &param_types, &captured, false, identity);
                Type::Fun(param_types, Box::new(ret))
            }
            Expr::Array(es, array_span) => {
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
                    // Numbers share their value join (nullable when one of
                    // them is); any other element type is the first one's.
                    let base = self
                        .numeric_element_type(es, &elem_tys)
                        .or_else(|| {
                            elem_tys
                                .iter()
                                .zip(es)
                                .find(|(_, e)| !matches!(e, Expr::Null(_)))
                                .map(|(t, _)| t.clone())
                        })
                        .unwrap_or_else(|| self.fresh_empty_array_elem());
                    if es.is_empty() && self.speculation_depth == 0 {
                        self.empty_array_elems.push((*array_span, base.clone()));
                    }
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
            Expr::TypeLit(name, fields, span) => {
                self.check_record_lit(name, fields, *span, None, scopes)
            }
            Expr::VariantLit(t, variant, fields, span) => {
                self.check_variant_lit(t, variant, fields, *span, scopes)
            }
            // A type test outside an `if` condition (the parser does not
            // produce this; hand-built ASTs only): a plain bool value.
            Expr::TypeTest(subject, _, _, _) => {
                self.check_expr(subject, scopes);
                Type::Bool
            }
            Expr::If(cond, then, els, span) if matches!(&**cond, Expr::TypeTest(..)) => {
                self.branch_expectation = None;
                let Expr::TypeTest(subject, te, negated, tspan) = &**cond else {
                    unreachable!("guarded by the arm pattern");
                };
                let _ = span;
                self.check_type_test_if(subject, te, *tspan, *negated, then, els.as_deref(), scopes)
            }
            Expr::If(cond, then, els, span) => {
                let expect = self.take_branch_expectation();
                let cond_ty = self.check_condition(cond, scopes);
                let mut truth = if self.is_narrowed_test(cond, scopes) {
                    None
                } else {
                    cond_ty.static_truthiness()
                };
                // Structural graceful degradation: a field access on an
                // ANONYMOUS structural record whose then-branch does not type
                // for this concrete value (a present field whose type the
                // branch's `return` cannot produce) folds the `if` to
                // statically false. That mirrors the back end exactly: the
                // call-site row view of such an argument drops a field that
                // does not fit the callee's use, so the condition reads an
                // absent member there (`never?`, false). A nominal record has
                // no view: its present field is truthy in the back end too, so
                // its then-branch is live and its conflicting `return` is a
                // type error, never a reason to skip an arm that runs.
                if truth != Some(false)
                    && let Expr::Field(base, ..) = &**cond
                    && self.is_structural_subject(base, scopes)
                {
                    let mark = self.errors.len();
                    let ends = self.narrowing_mark();
                    let mut probe = scopes.clone();
                    self.apply_truthy_narrowing(cond, &mut probe);
                    // Isolate the probe's collected returns: they describe the
                    // (possibly dead) arm, not the enclosing callable, and the
                    // real walk below re-collects the live ones.
                    self.return_values.push(Vec::new());
                    self.discarded_walk(true, |this| {
                        this.check_branch(then, &mut probe, false, expect.as_ref())
                    });
                    let probe_returns = self.return_values.pop().unwrap_or_default();
                    let failed = self.errors.len() > mark;
                    self.errors.truncate(mark);
                    self.narrowing_ends_since(ends);
                    if failed && self.then_branch_return_conflicts(then, &probe_returns) {
                        truth = Some(false);
                    }
                }
                let ends = self.narrowing_mark();
                let mut then_scopes = scopes.clone();
                self.apply_truthy_narrowing(cond, &mut then_scopes);
                // A statically-known condition makes one arm unreachable. Its
                // body is still walked (so nested call instances are recorded for
                // monomorphization) but its type errors are discarded: a dead
                // path may not type-check -- e.g. a bare `null` (`never?`) whose
                // truthy arm narrows it to `never` -- yet must not reject the
                // program. Its `return`s do not join (see `check_branch`), and
                // the per-instance light walk prunes the same arm (see
                // `record_static_fold`), so its error sites do not make the
                // instance fallible. The reachable arm alone determines the
                // `if` type.
                let then_ty = self.check_branch(
                    then,
                    &mut then_scopes,
                    truth == Some(false),
                    expect.as_ref(),
                );
                let then_ends = self.narrowing_ends_since(ends);
                let else_ty = match els {
                    Some(e) => {
                        self.check_branch_expr(e, scopes, truth == Some(true), expect.as_ref())
                    }
                    None => Type::Void,
                };
                // Narrowings an arm ends stay ended where its path continues.
                let else_ends = self.narrowing_ends_since(ends);
                let then_exit = ArmExit::of_block(then).unless_dead(truth == Some(false));
                let else_exit = els
                    .as_deref()
                    .map_or(ArmExit::FallsThrough, ArmExit::of_expr)
                    .unless_dead(truth == Some(true));
                self.route_arm_ends(then_ends, then_exit);
                self.route_arm_ends(else_ends, else_exit);
                self.record_static_fold(*span, truth);
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
                    None => {
                        let branches = [
                            (then_ty, block_literal(then)),
                            (else_ty, els.as_deref().and_then(value_literal)),
                        ];
                        self.join_branch_types("if", branches, expect.as_ref(), *span)
                    }
                }
            }
            Expr::IfLet(pat, scrut, then, els, span) => {
                let expect = self.take_branch_expectation();
                let scrut_ty = self.check_expr(scrut, scopes);
                self.check_pattern_against(&scrut_ty, pat);
                self.check_out_of_scope_variant_binding(&scrut_ty, pat);
                let mut then_scopes = scopes.clone();
                then_scopes.push(Scope::default());
                self.const_scopes.push(HashSet::default());
                // A plain binding on a nullable scrutinee is a presence test, so on
                // the then-arm the value is proven non-null: bind it at the unwrapped
                // type (e.g. `if let p = T.from(v)` gives `p: T`), so `p.field` is
                // valid rather than a nullable-use error. A reference parameter
                // (`ref(T?)`, `ref(mut(T?))`, `mut(T?)`) is tested through its
                // reference like any other nullable.
                let resolved_scrut = self.resolve(&scrut_ty);
                let bind_ty = match (pat, peel_ref_mut(&resolved_scrut)) {
                    (Pattern::Binding(_, None, _), Type::Nullable(inner)) => (**inner).clone(),
                    _ => scrut_ty.clone(),
                };
                self.bind_pattern(pat, &bind_ty, &mut then_scopes);
                // A plain binding is a presence test the scrutinee's type may
                // decide, exactly like `if v.f` (types.md, Absent fields): an
                // absent member (`never?`) never binds, a present non-nullable
                // value always does. The arm that cannot run is walked but not
                // checked and contributes no returns; the back end folds the
                // same test. A narrowed scrutinee is tested at run time (the
                // back end sees its declared nullable), and a sum scrutinee's
                // name may be one of its unit variants.
                let truth = match pat {
                    Pattern::Binding(_, None, _)
                        if !self.is_narrowed_test(scrut, scopes)
                            && !matches!(peel_ref_mut(&resolved_scrut), Type::Sum(_)) =>
                    {
                        presence_binding_truth(&resolved_scrut)
                    }
                    _ => None,
                };
                let ends = self.narrowing_mark();
                let then_ty = self.check_branch(
                    then,
                    &mut then_scopes,
                    truth == Some(false),
                    expect.as_ref(),
                );
                self.const_scopes.pop();
                let then_ends = self.narrowing_ends_since(ends);
                let else_ty = match els {
                    Some(e) => {
                        self.check_branch_expr(e, scopes, truth == Some(true), expect.as_ref())
                    }
                    None => Type::Void,
                };
                let else_ends = self.narrowing_ends_since(ends);
                self.route_arm_ends(
                    then_ends,
                    ArmExit::of_block(then).unless_dead(truth == Some(false)),
                );
                let else_exit = els
                    .as_deref()
                    .map_or(ArmExit::FallsThrough, ArmExit::of_expr)
                    .unless_dead(truth == Some(true));
                self.route_arm_ends(else_ends, else_exit);
                self.record_static_fold(*span, truth);
                // As for a folded `if`: a selected arm that always returns
                // leaves the rest of the block unreachable.
                self.static_divergence = match truth {
                    Some(true) => block_always_returns(then),
                    Some(false) => els.as_deref().is_some_and(expr_always_returns),
                    None => false,
                };
                match truth {
                    Some(true) => then_ty,
                    Some(false) => else_ty,
                    None => {
                        let branches = [
                            (then_ty, block_literal(then)),
                            (else_ty, els.as_deref().and_then(value_literal)),
                        ];
                        self.join_branch_types("if-let", branches, expect.as_ref(), *span)
                    }
                }
            }
            Expr::Match(scrut, arms, span) => {
                let expect = self.take_branch_expectation();
                let scrut_ty = self.check_expr(scrut, scopes);
                self.check_unreachable_arms(&scrut_ty, arms, scopes);
                let ends = self.narrowing_mark();
                let mut arm_ends = Vec::with_capacity(arms.len());
                let mut branches = Vec::with_capacity(arms.len());
                for arm in arms {
                    self.check_pattern_against(&scrut_ty, &arm.pattern);
                    self.check_out_of_scope_variant_binding(&scrut_ty, &arm.pattern);
                    let mut arm_scopes = scopes.clone();
                    arm_scopes.push(Scope::default());
                    self.const_scopes.push(HashSet::default());
                    self.bind_pattern(&arm.pattern, &scrut_ty, &mut arm_scopes);
                    let arm_ty =
                        self.check_branch_value(&arm.body, expect.as_ref(), &mut arm_scopes);
                    self.const_scopes.pop();
                    // Each arm starts from the narrowings in force before the
                    // `match`; its ends are routed once every arm is checked.
                    arm_ends.push((self.narrowing_ends_since(ends), ArmExit::of_expr(&arm.body)));
                    branches.push((arm_ty, value_literal(&arm.body)));
                }
                for (ended, exit) in arm_ends {
                    self.route_arm_ends(ended, exit);
                }
                self.join_branch_types("match", branches, expect.as_ref(), *span)
            }
            Expr::Block(b, _) => {
                let expect = self.take_branch_expectation();
                self.check_block_expr(b, scopes, expect)
            }
        }
    }

    /// The error-free join of two non-numeric branch types for the light
    /// walk: their common nullable, `left` when they unify or are
    /// structurally compatible, else a fresh variable.
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

    /// The type of a value-producing `if`/`match`: the join of its branch
    /// values, each given as its type and, when the branch's value is written
    /// as a numeric literal, that literal's value. Numeric branches (with
    /// `null` or nullable numbers among them) meet by the shared join rule
    /// (`brass_typesys::join_values`): every branch value flows into the
    /// result with the value-preserving conversions, and a literal branch
    /// adapts, so `if c { an_int64 } else { 0 }` is `int64`. Any other
    /// branches must agree pairwise. In statement position the expression
    /// has no value and nothing is joined (see
    /// [`Self::statement_branch_type`]).
    ///
    /// When the value flows into a numeric requirement (`expect`), the
    /// branches written as literals first adapt to it, exactly like a literal
    /// flowing into that slot directly -- provided every one of them fits:
    /// `let small: uint8 = if c { 200 } else { 7 }` is a `uint8`. The other
    /// branches keep their own types; the join then flows into the slot.
    pub(super) fn join_branch_types(
        &mut self,
        context: &str,
        branches: impl IntoIterator<Item = (Type, Option<brass_typesys::NumericLiteral>)>,
        expect: Option<&(Type, FlowSite)>,
        span: brass_parser::Span,
    ) -> Type {
        let mut branches: Vec<(Type, Option<brass_typesys::NumericLiteral>)> =
            branches.into_iter().collect();
        if let Some(ty) = self.statement_branch_type(span, branches.iter().map(|(ty, _)| ty)) {
            return ty;
        }
        let mut adapted = false;
        if let Some(target) = expect.and_then(|(want, _)| numeric_requirement(&self.resolve(want)))
        {
            let literals = branches.iter().filter_map(|(_, lit)| *lit);
            let mut literals = literals.peekable();
            if literals.peek().is_some() && literals.all(|lit| lit.fits(&target)) {
                for branch in branches.iter_mut().filter(|(_, lit)| lit.is_some()) {
                    *branch = (target.clone(), None);
                }
                adapted = true;
            }
        }
        if let Some(joined) = self.numeric_branch_join(&branches) {
            if adapted {
                // The back end joins the bare literal values at their
                // default type; the adapted join is recorded for it.
                self.record_typed(
                    brass_hir::TypedExprKind::LiteralBranchJoin,
                    span,
                    self.resolve(&joined),
                    brass_hir::Constness::Unknown,
                );
            }
            return joined;
        }
        let mut types = branches.into_iter().map(|(ty, _)| ty);
        let Some(first) = types.next() else {
            return Type::Void;
        };
        types.fold(first, |acc, ty| {
            self.common_type_or_error(context, acc, ty, span)
        })
    }

    /// [`Self::join_branch_types`]'s numeric case: `Some` when every branch
    /// that yields a value is a number, `null`, or a nullable number, and they
    /// have a join by the value join ([`brass_typesys::join_values`], the rule
    /// returns join by too). A diverging (`never`) branch constrains nothing.
    pub(super) fn numeric_branch_join(
        &self,
        branches: &[(Type, Option<brass_typesys::NumericLiteral>)],
    ) -> Option<Type> {
        let mut nullable = false;
        let mut values: Vec<(Type, Option<brass_typesys::NumericLiteral>)> =
            Vec::with_capacity(branches.len());
        for (ty, literal) in branches {
            match self.resolve(ty) {
                Type::Never => {}
                t if t.is_null() => nullable = true,
                Type::Nullable(inner) if matches!(*inner, Type::Int(_) | Type::Float(_)) => {
                    nullable = true;
                    values.push((*inner, None));
                }
                t @ (Type::Int(_) | Type::Float(_)) => values.push((t, *literal)),
                _ => return None,
            }
        }
        if values.is_empty() {
            return None;
        }
        let operands: Vec<brass_typesys::JoinOperand> = values
            .into_iter()
            .map(|(ty, literal)| brass_typesys::JoinOperand { ty, literal })
            .collect();
        let joined = brass_typesys::join_values(self.program, &operands).ok()??;
        Some(if nullable {
            Type::Nullable(Box::new(joined))
        } else {
            joined
        })
    }

    fn common_type_or_error(
        &mut self,
        context: &str,
        left: Type,
        right: Type,
        span: brass_parser::Span,
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
        if self.can_unify(&left, &right) {
            // COMMIT the unification, do not merely probe it: both branches of
            // one `if` yield one type, so binding them together is what the
            // expression means. A branch whose type nothing else constrains --
            // `else { error("..")! }`, whose Ok payload is a fresh variable no
            // path produces -- would otherwise reach the back end unresolved,
            // with no type for the value it stores into the `if`'s slot.
            let _ = self.solver.unify(&left, &right);
            return left;
        }
        if crate::structural::types_compatible(self.program, &left, &right) {
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

    /// Type `if subject: T { then } else { els }` -- the compile-time
    /// type-test dispatch. Each monomorphic instance decides the test
    /// statically: the subject's resolved type either matches the annotation
    /// (through `brass_typesys::type_test_accepts`, the same predicate the
    /// back ends fold the branch with) and the then-arm alone is checked
    /// live, or it does not and the else-arm alone is. The unselected arm is
    /// walked with its errors discarded and its `return`s isolated -- it is
    /// code this instance never compiles.
    ///
    /// `infer` holes in the annotation mean "whatever the tested arm
    /// requires": before deciding, the matching arm (else for a negated test)
    /// is probed once with the subject bound to the freshened pattern, so a
    /// concrete requirement the arm places on the subject (`to_bytes(v)`
    /// demanding `string`) pins the hole; a hole nothing pins stays a
    /// wildcard that matches any type. The probe is fully rolled back. The
    /// pinned pattern is recorded on the `type_tests` channel for MIR (shared
    /// across instantiations, so a disagreement is rejected).
    ///
    /// A subject whose type is still open (the definitional pass of a generic
    /// body) selects nothing: every arm is walked speculatively with errors
    /// discarded and constraints rolled back, and the `if` types as a fresh
    /// variable. Each instantiation then decides and checks for real.
    #[allow(clippy::too_many_arguments)]
    fn check_type_test_if(
        &mut self,
        subject: &Expr,
        te: &brass_parser::ast::TypeExpr,
        test_span: brass_parser::Span,
        negated: bool,
        then: &Block,
        els: Option<&Expr>,
        scopes: &mut ScopeStack,
    ) -> Type {
        let subject_ty = self.check_expr(subject, scopes);
        let subject_ty = self.resolve(&subject_ty);
        let pattern = match self.resolve_type(te) {
            Ok(t) => t,
            Err(message) => {
                self.errors.push(TypeError {
                    message,
                    span: te.span(),
                });
                Type::Unknown(brass_hir::INFER_VAR)
            }
        };
        // `resolve_type` already freshens each `infer` (and `typeof`) hole
        // into its own inference variable; those variables ARE the holes the
        // probe may pin. They are freshly minted for this annotation, so no
        // outer binding shares them.
        let hole_ids: Vec<u32> = self.solver.free_vars(&pattern).into_iter().collect();
        // Probe the tested arm at the pattern to pin its holes. Also reused
        // as the speculative then-walk when the subject is still open.
        let snap = self.solver.snapshot();
        let mark = self.errors.len();
        let ends = self.narrowing_mark();
        let mut probe_scopes = scopes.clone();
        if let Expr::Ident(name, _) = subject {
            let mut frame: HashMap<String, Type> = HashMap::default();
            frame.insert(name.clone(), pattern.clone());
            probe_scopes.push(Scope::new(frame));
        }
        if !hole_ids.is_empty() {
            self.type_test_holes.extend(hole_ids.iter().copied());
        }
        self.return_values.push(Vec::new());
        self.speculation_depth += 1;
        if negated {
            if let Some(e) = els {
                self.check_branch_expr(e, &mut probe_scopes, true, None);
            }
        } else {
            self.check_branch(then, &mut probe_scopes, true, None);
        }
        self.speculation_depth -= 1;
        self.return_values.pop();
        for id in &hole_ids {
            self.type_test_holes.remove(id);
        }
        let probed = self.resolve(&pattern);
        self.errors.truncate(mark);
        self.narrowing_ends_since(ends);
        self.solver.rollback(snap);
        self.static_divergence = false;
        let pattern = wildcard_open_vars(&probed);

        if brass_hir::is_fully_known(&subject_ty) {
            self.record_type_test(test_span, &pattern);
            let matched =
                brass_typesys::type_test_accepts(self.program, &pattern, &subject_ty) != negated;
            self.record_static_fold(test_span, Some(matched));
            // The dead arm is walked but contributes NOTHING to this
            // instance: its errors are discarded, its `return`s isolated and
            // the narrowings it ends dropped. Monomorphization mirrors this
            // exactly -- a type-test-dead block is never typed, joins no
            // return and supplies no error site (`type_test_live_blocks`) --
            // so an `error(...)` on an unselected path does not make this
            // instance's ABI a `Result`.
            let mut then_scopes = scopes.clone();
            let chosen = if matched {
                let then_ty = self.check_branch(then, &mut then_scopes, false, None);
                if let Some(e) = els {
                    let ends = self.narrowing_mark();
                    self.return_values.push(Vec::new());
                    self.check_branch_expr(e, scopes, true, None);
                    self.return_values.pop();
                    self.narrowing_ends_since(ends);
                }
                then_ty
            } else {
                let ends = self.narrowing_mark();
                self.return_values.push(Vec::new());
                self.check_branch(then, &mut then_scopes, true, None);
                self.return_values.pop();
                self.narrowing_ends_since(ends);
                match els {
                    Some(e) => self.check_branch_expr(e, scopes, false, None),
                    None => Type::Void,
                }
            };
            // A `Never`-typed selection diverges (its arm always leaves), so
            // the rest of the enclosing block is unreachable for this
            // instance. The syntactic always-returns probe cannot see through
            // a statically-decided nested chain; the selected arm's type can.
            // The statements it kills also stop contributing returns
            // (`check_block` isolates them): the fall-through after a selected
            // always-returning arm is not this instance's code.
            self.static_divergence = matches!(self.resolve(&chosen), Type::Never);
            chosen
        } else {
            let snap = self.solver.snapshot();
            let mark = self.errors.len();
            let ends = self.narrowing_mark();
            self.return_values.push(Vec::new());
            self.speculation_depth += 1;
            if negated {
                self.check_branch(then, &mut scopes.clone(), true, None);
            } else if let Some(e) = els {
                self.check_branch_expr(e, scopes, true, None);
            }
            self.speculation_depth -= 1;
            self.return_values.pop();
            self.errors.truncate(mark);
            self.narrowing_ends_since(ends);
            self.solver.rollback(snap);
            self.static_divergence = false;
            self.fresh_unknown()
        }
    }

    /// Record a decided type test's pattern for MIR lowering, rejecting a
    /// shared generic body whose instantiations pin a hole differently (one
    /// lowering serves them all, so no single pattern would be right).
    pub(super) fn record_type_test(&mut self, span: brass_parser::Span, pattern: &Type) {
        self.journal_elaboration(ElaborationJournalEntry::TypeTest(span, pattern.clone()));
        if self.type_test_poisoned.contains(&span) {
            return;
        }
        self.channel_changes
            .get_mut()
            .mark(channel_changes::Channel::TypeTest, span);
        match self.type_tests.get(&span) {
            None => {
                self.type_tests.insert(span, pattern.clone());
            }
            Some(prev) if prev == pattern => {}
            Some(_) => {
                self.type_tests.remove(&span);
                self.type_test_poisoned.insert(span);
                self.errors.push(TypeError {
                    message: "this type test resolves its `infer` holes differently across \
                              instantiations of this generic function; the shared lowering \
                              can only fold one pattern (annotate the tested type)"
                        .to_string(),
                    span,
                });
            }
        }
    }

    /// Type an `if` block arm, discarding its errors when `dead` (statically
    /// unreachable). The arm is still walked so its nested call instances reach
    /// monomorphization; only the type errors -- which a dead path is allowed to
    /// have -- are rolled back, and its `return`s are isolated: code this
    /// instance never runs does not join its return type (monomorphization
    /// joins only the reachable returns too).
    fn check_branch(
        &mut self,
        b: &Block,
        scopes: &mut ScopeStack,
        dead: bool,
        expect: Option<&(Type, FlowSite)>,
    ) -> Type {
        let mark = self.errors.len();
        if dead {
            self.return_values.push(Vec::new());
        }
        let ty = self.discarded_walk(dead, |this| {
            this.check_block_expr(b, scopes, expect.cloned())
        });
        if dead {
            self.return_values.pop();
            self.errors.truncate(mark);
        }
        ty
    }

    /// As `check_branch`, for an `else` arm (a nested expression rather than a
    /// block; an `else if` chain or a braced block lowered to an expression).
    fn check_branch_expr(
        &mut self,
        e: &Expr,
        scopes: &mut ScopeStack,
        dead: bool,
        expect: Option<&(Type, FlowSite)>,
    ) -> Type {
        let mark = self.errors.len();
        if dead {
            self.return_values.push(Vec::new());
        }
        let ty = self.discarded_walk(dead, |this| this.check_branch_value(e, expect, scopes));
        if dead {
            self.return_values.pop();
            self.errors.truncate(mark);
        }
        ty
    }

    /// Check a branch value of an `if`/`match`/block whose value flows into
    /// `expect`. A construction requirement checks the value against it (the
    /// value adapts and flows there). A numeric one is not a per-branch flow:
    /// the branch values join first and the join flows (so a mismatch is
    /// reported once); it only reaches a nested branching value, whose
    /// literal branches adapt to it as well.
    pub(super) fn check_branch_value(
        &mut self,
        e: &Expr,
        expect: Option<&(Type, FlowSite)>,
        scopes: &mut ScopeStack,
    ) -> Type {
        let Some((want, site)) = expect else {
            return self.check_expr(e, scopes);
        };
        if brass_typesys::shapes_constructions(&self.resolve(want)) {
            return self.check_expr_against_at(e, want, *site, scopes);
        }
        if matches!(
            e,
            Expr::If(..) | Expr::IfLet(..) | Expr::Match(..) | Expr::Block(..)
        ) {
            self.branch_expectation = Some((want.clone(), *site));
            let ty = self.check_expr(e, scopes);
            self.branch_expectation = None;
            return ty;
        }
        self.check_expr(e, scopes)
    }

    /// Record the static decision of the `if`/`if let` at `span` for the body
    /// being checked (see `Checker::static_fold_frames`). A dead walk's
    /// decisions describe code that does not run and are not recorded.
    fn record_static_fold(&mut self, span: brass_parser::Span, truth: Option<bool>) {
        if self.discarded_walks > 0 {
            return;
        }
        if let (Some(truth), Some(frame)) = (truth, self.static_fold_frames.last_mut()) {
            frame.insert(span, truth);
        }
    }

    /// Whether a structural `if` on an anonymous record's field may fold
    /// false: the then-branch reaches a `return <value>` through straight-line
    /// statements only, and the returned value's primitive kind clearly
    /// conflicts with the enclosing declared return type (its Ok payload for a
    /// fallible signature) -- the field the row view drops as not fitting.
    fn then_branch_return_conflicts(
        &mut self,
        then: &Block,
        probe_returns: &[(Type, brass_parser::Span)],
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
        let ty = self.resolve_head(ty);
        // A returned `Result` flows whole rather than as the Ok payload; the
        // back end never folds on it.
        if ty.is_result_type() {
            return false;
        }
        brass_hir::primitive_kind_conflict(&ty, &target)
    }

    /// Whether the field base `base` is a value of an anonymous structural
    /// record type (`{ name: .. }`), whose call-site row view degrades a
    /// field that does not fit the use to absent.
    fn is_structural_subject(&mut self, base: &Expr, scopes: &ScopeStack) -> bool {
        let ty = match base {
            Expr::Ident(name, _) => self.lookup(scopes, name),
            _ => None,
        };
        ty.is_some_and(|ty| {
            matches!(
                brass_hir::peel_modes(&self.resolve(&ty)),
                Type::Record(n) if n.id == brass_hir::STRUCTURAL_RECORD_ID
            )
        })
    }

    /// Check a block in expression position: its trailing expression is its
    /// value, which flows into `expect` when the block is a branch of an
    /// expression with a requirement (see `Checker::branch_expectation`).
    ///
    /// The block's type is its trailing expression's, or `void` when it ends
    /// in a statement.
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
    /// Typed `void`, that arm would make the join report `int32` and `void` as
    /// incompatible. Divergence anywhere in the block counts, not just in its last
    /// statement: whatever follows a `return` is unreachable, so the block still
    /// yields nothing.
    ///
    /// The statements themselves are checked by the shared walker
    /// ([`Self::check_block_stmts`]), exactly as in a statement block.
    fn check_block_expr(
        &mut self,
        b: &Block,
        scopes: &mut ScopeStack,
        expect: Option<(Type, FlowSite)>,
    ) -> Type {
        // Only the trailing expression is the block's value; every earlier
        // expression statement's value is discarded (see `check_stmt`).
        let tail = match b.stmts.last() {
            Some(Stmt::Expr(e)) => Some(e.span()),
            _ => None,
        };
        let saved = std::mem::replace(&mut self.block_value_tail, tail);
        let saved_expect = std::mem::replace(&mut self.tail_expectation, expect);
        let ty = self.check_block_stmts(b, scopes);
        self.block_value_tail = saved;
        self.tail_expectation = saved_expect;
        ty
    }

    /// Type the assignment target `e` and return the type a store into it
    /// must flow into: a variable, `self`, or a field or index projection of
    /// one. A string index and any other expression are rejected as targets.
    pub(super) fn check_place(&mut self, e: &Expr, scopes: &mut ScopeStack) -> Type {
        let ty = match e {
            Expr::Field(base, name, span) => self.check_field(base, name, *span, scopes),
            Expr::Index(base, idx, span) => {
                let base_ty = self.check_expr(base, scopes);
                let idx_ty = self.check_expr(idx, scopes);
                self.expect_int_index(&idx_ty, idx.span());
                let resolved = self.resolve(&base_ty);
                if let Some(elem) = brass_hir::index_element(&resolved) {
                    return elem;
                }
                match brass_hir::peel_modes(&resolved).clone() {
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
        let ty = self.check_null_test_operand(cond, scopes);
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

    /// The element type of `[lo..hi]` (and the type a `for` over it counts
    /// in): the type the bounds meet at by the operator rule
    /// (`brass_typesys::common_operand_type`), exactly as `lo < hi` types its
    /// operands. A literal bound adapts to the other bound when its value fits,
    /// so counting over a length runs at the length's width (`[0..a.len()]` is
    /// `int64[]`); otherwise the bounds take their common type, so a narrow
    /// `lo` with a wider `hi` counts at the wider type and reaches `hi`
    /// (`[lo..256]` with `lo: uint8` is `int32[]`).
    fn range_element_type(&mut self, lo_ty: &Type, lo: &Expr, hi_ty: &Type, hi: &Expr) -> Type {
        let lo_r = peel_value_wrappers(&self.resolve(lo_ty)).clone();
        let hi_r = peel_value_wrappers(&self.resolve(hi_ty)).clone();
        match (&lo_r, &hi_r) {
            // An open bound (still being inferred) follows the other side.
            (Type::Unknown(_), _) => hi_r,
            (_, Type::Unknown(_)) => lo_r,
            (Type::Int(_), Type::Int(_)) => {
                let common = brass_typesys::common_operand_type(
                    brass_typesys::NumericOperand::new(
                        &lo_r,
                        brass_typesys::NumericLiteral::of_expr(lo),
                    ),
                    brass_typesys::NumericOperand::new(
                        &hi_r,
                        brass_typesys::NumericLiteral::of_expr(hi),
                    ),
                );
                if let Some(t) = common {
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

    fn expect_int_index(&mut self, ty: &Type, span: brass_parser::Span) {
        match self.resolve(ty) {
            Type::Int(_) | Type::Unknown(_) => {}
            other => self.errors.push(TypeError {
                message: format!("index must be an integer, found `{}`", other.display()),
                span,
            }),
        }
    }

    /// The element type of a bracket literal whose non-null elements are all
    /// numbers that join ([`brass_typesys::numeric_element_join`]): a literal
    /// element adapts to the others, typed ones meet at their common type.
    pub(super) fn numeric_element_type(&self, elems: &[Expr], elem_tys: &[Type]) -> Option<Type> {
        let operands: Vec<brass_typesys::JoinOperand> = elems
            .iter()
            .zip(elem_tys)
            .filter(|(e, _)| !matches!(e, Expr::Null(_)))
            .map(|(e, t)| brass_typesys::JoinOperand {
                ty: self.resolve(t),
                literal: brass_typesys::NumericLiteral::of_expr(e),
            })
            .collect();
        brass_typesys::numeric_element_join(self.program, &operands)
    }

    /// If a bracket literal's elements describe a tuple, return their types; else
    /// `None` (an array). Numbers that join make an array; otherwise a
    /// rolled-back probe over each element's representative type (a numeric
    /// literal stands in as its default kind, not its open variable) decides
    /// array-vs-tuple, and a tuple returns the elements' actual types so an
    /// annotation can still fix widths.
    pub(super) fn tuple_of_elements(
        &mut self,
        elems: &[Expr],
        elem_tys: &[Type],
    ) -> Option<Vec<Type>> {
        if elems.len() < 2 || self.numeric_element_type(elems, elem_tys).is_some() {
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
        // Independent unresolved element types must not be coupled by a
        // speculative array classification. Keep their positions separate
        // until concrete elaboration decides the shape. This also preserves
        // the distinct key/value variables in `HashMap.pairs`.
        let provisional = reps.iter().any(|ty| !brass_hir::is_fully_known(ty))
            && rest.iter().any(|ty| ty != first);
        if provisional {
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

/// Replace every still-open inference variable in a probed type-test pattern
/// with the `infer` wildcard. A hole nothing pinned means "matches anything",
/// and a leftover solver id would differ between instantiations (and between
/// the checker and MIR), so the recorded pattern must carry none.
pub(super) fn wildcard_open_vars(ty: &Type) -> Type {
    use brass_hir::{NominalType, Substitution};
    match ty {
        Type::Unknown(_) => Type::Unknown(brass_hir::INFER_VAR),
        Type::Slice(e) => Type::Slice(Box::new(wildcard_open_vars(e))),
        Type::Array(e, n) => Type::Array(Box::new(wildcard_open_vars(e)), *n),
        Type::Nullable(e) => Type::Nullable(Box::new(wildcard_open_vars(e))),
        Type::ConstOf(e) => Type::ConstOf(Box::new(wildcard_open_vars(e))),
        Type::Mut(e) => Type::Mut(Box::new(wildcard_open_vars(e))),
        Type::Ref(e) => Type::Ref(Box::new(wildcard_open_vars(e))),
        Type::Fun(ps, r) => Type::Fun(
            ps.iter().map(wildcard_open_vars).collect(),
            Box::new(wildcard_open_vars(r)),
        ),
        Type::Tuple(es) => Type::Tuple(es.iter().map(wildcard_open_vars).collect()),
        Type::Record(n) | Type::Sum(n) => {
            let mut subst = Substitution::empty();
            for (k, v) in n.substitution.iter() {
                subst.insert(k, wildcard_open_vars(v));
            }
            let rebuilt = NominalType::with_substitution(n.id, n.name().to_string(), subst);
            match ty {
                Type::Record(_) => Type::Record(rebuilt),
                _ => Type::Sum(rebuilt),
            }
        }
        other => other.clone(),
    }
}

/// The spans of the `!` operators in a closure body that propagate out of
/// that closure: those of a closure nested in the body propagate out of the
/// nested one instead.
fn own_error_props(body: &Expr) -> Vec<brass_parser::Span> {
    use crate::walk::{ExprVisitor, walk_expr};
    #[derive(Default)]
    struct Props {
        all: Vec<brass_parser::Span>,
        nested: HashSet<brass_parser::Span>,
    }
    struct Nested<'a>(&'a mut HashSet<brass_parser::Span>);
    impl ExprVisitor for Nested<'_> {
        fn visit(&mut self, e: &Expr) {
            if let Expr::ErrorProp(_, span) = e {
                self.0.insert(*span);
            }
        }
    }
    impl ExprVisitor for Props {
        fn visit(&mut self, e: &Expr) {
            match e {
                Expr::ErrorProp(_, span) => self.all.push(*span),
                Expr::Closure(_, inner, _) => walk_expr(inner, &mut Nested(&mut self.nested)),
                _ => {}
            }
        }
    }
    let mut props = Props::default();
    walk_expr(body, &mut props);
    let Props { all, nested } = props;
    all.into_iter().filter(|s| !nested.contains(s)).collect()
}

/// The numeric type a requirement fixes for a literal flowing into it: the
/// number itself, or the present value of a nullable number.
fn numeric_requirement(want: &Type) -> Option<Type> {
    match brass_hir::peel_modes(want) {
        Type::Nullable(inner) => numeric_requirement(inner),
        t @ (Type::Int(_) | Type::Float(_)) => Some(t.clone()),
        _ => None,
    }
}
