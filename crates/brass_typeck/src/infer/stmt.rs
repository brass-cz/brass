//! Block and statement checking: function and method body roots, the one
//! statement walker behind statement and expression blocks (with the
//! fall-through a statically folded `if` makes unreachable), `return`
//! against the active return context, `let` (annotations with `typeof`,
//! uninitialized bindings), assignments, `while`/`for` loops, and the
//! per-field expansion of `for f in fields(x)`.

use super::*;

impl Checker<'_> {
    /// Check a method body with `self` bound to the bare type. For an
    /// inferred-return body, returns the reconciled return type like
    /// [`Self::check_block_root`].
    pub(super) fn check_block_with_self(
        &mut self,
        b: &Block,
        scopes: &mut ScopeStack,
        ret: Option<&Type>,
        self_type: &str,
    ) -> Option<Type> {
        self.check_block_with_self_context(b, scopes, ret, self_type, None)
    }

    /// Check the body of a method declared on the variant `variant` of the
    /// sum `self_type`: `self` is the sum, and `self.field` reads the
    /// variant's own payload fields.
    pub(super) fn check_block_with_self_variant(
        &mut self,
        b: &Block,
        scopes: &mut ScopeStack,
        ret: Option<&Type>,
        self_type: &str,
        variant: &str,
    ) {
        self.check_block_with_self_context(b, scopes, ret, self_type, Some(variant));
    }

    fn check_block_with_self_context(
        &mut self,
        b: &Block,
        scopes: &mut ScopeStack,
        ret: Option<&Type>,
        self_type: &str,
        variant: Option<&str>,
    ) -> Option<Type> {
        let saved = self.self_type.replace(self_type.to_string());
        let saved_variant = self.self_variant.clone();
        self.self_variant = variant.map(|v| (self_type.to_string(), v.to_string()));
        if let Some(scope) = scopes.last_mut() {
            scope.insert("self".to_string(), self.type_by_name(self_type));
        }
        let full = self.check_block_root(b, scopes, ret);
        self.self_type = saved;
        self.self_variant = saved_variant;
        full
    }

    /// Check a function/method body. For an inferred-return body (`ret` is `None`)
    /// returns the reconciled type of its `return` values as observed by the full
    /// check (so a constructor whose slot array is filled with `null` returns the
    /// nullable element type), or `None` for an explicit-return body.
    pub(super) fn check_block_root(
        &mut self,
        b: &Block,
        scopes: &mut ScopeStack,
        ret: Option<&Type>,
    ) -> Option<Type> {
        let numeric_root = !self.numeric.active
            && !self.numeric_zero_growth
            && (self.numeric_enabled || self.lazy_profile);
        if numeric_root
            && (self
                    .numeric_eligibility
                    .get()
                    .is_some_and(|index| index.transitive(b.span))
                || self.numeric_body_is_settled()
                || self.numeric_body_is_locally_closed(b, scopes)
                // Repeated nested roots amortize the shared graph and avoid
                // rebuilding ordinary memo keys throughout a pure call tree.
                || (self.instance_stack.len() > 1
                    && self.numeric_eligibility().transitive(b.span)))
        {
            let enabled = std::mem::replace(&mut self.numeric_enabled, false);
            self.numeric_zero_growth = true;
            let result = self.check_block_root(b, scopes, ret);
            self.numeric_zero_growth = false;
            self.numeric_enabled = enabled;
            return result;
        }
        if numeric_root && self.numeric_unsettled_body_needs_settlement(b, scopes) {
            let enabled = std::mem::replace(&mut self.numeric_enabled, true);
            let mut settled = self.settle_numeric_body(b, scopes, ret);
            tracing::debug!(callable = ?self.current_instance().map(|tag| tag.callable.clone()), changed = settled.changed, "settled numeric body");
            let zero = std::mem::replace(&mut self.numeric_zero_growth, !settled.changed);
            if !settled.changed {
                self.numeric_enabled = false;
                settled = Default::default();
            }
            let saved = std::mem::replace(&mut self.numeric, settled);
            let result = self.check_block_root(b, scopes, ret);
            self.numeric = saved;
            self.numeric_enabled = enabled;
            self.numeric_zero_growth = zero;
            return result;
        }
        if self.numeric.probing {
            self.enter_numeric_body(b.span);
            self.numeric.returns.push(Vec::new());
        }
        let saved = std::mem::replace(&mut self.const_scopes, vec![HashSet::default()]);
        let saved_kills = std::mem::take(&mut self.narrowing_kills);
        let saved_loops = std::mem::take(&mut self.loop_frames);
        let saved_facts = std::mem::replace(
            &mut self.narrowing_facts,
            Rc::new(narrowing::NarrowingFacts::of_stmts(&b.stmts)),
        );
        self.return_contexts.push(match ret {
            Some(ty) => ReturnContext::Explicit(ty.clone()),
            None => ReturnContext::Inferred,
        });
        self.return_values.push(Vec::new());
        self.static_fold_frames.push(HashMap::default());
        let saved_divergence = std::mem::take(&mut self.diverging_exprs);
        let end = self.check_block_stmts(b, scopes);
        self.last_static_folds = self.static_fold_frames.pop().unwrap_or_default();
        let diverges = matches!(self.resolve(&end), Type::Never)
            || crate::flow::block_diverges(
                self.program,
                &self.current_module,
                b,
                &self.diverging_exprs,
                &self.last_static_folds,
            );
        self.diverging_exprs = saved_divergence;
        let mut collected = self.return_values.pop().unwrap_or_default();
        if ret.is_none()
            && scopes.last().is_none_or(|frame| {
                frame
                    .values()
                    .all(|ty| brass_hir::is_fully_known(&self.resolve(ty)))
            })
        {
            self.collect_body_end(b, diverges, &mut collected);
        }
        self.last_returns = collected.clone();
        if self.numeric.probing {
            let origins = self.numeric.returns.pop().unwrap_or_default();
            self.numeric.result = if ret.is_none()
                && !origins.is_empty()
                && origins.iter().all(|source| *source == origins[0])
            {
                origins[0].clone()
            } else {
                None
            };
        }
        self.return_contexts.pop();
        self.narrowing_facts = saved_facts;
        self.loop_frames = saved_loops;
        self.narrowing_kills = saved_kills;
        self.const_scopes = saved;
        let result = if ret.is_none() {
            // The co-check RECORDS the unifiable-return links (see
            // `reconcile_return_types_with`): this is what ties a method's
            // open-parameter return to the value it joins with, so the scheme
            // records them as one parameter (`get_or`'s `dflt` IS the map's
            // value type).
            let common = self.reconcile_return_types_with(&collected, false, self.co_checking);
            if let Some(joined) = &common {
                self.record_return_rebuilds(&collected, joined);
            }
            // The join helper leaves an open variable bare when joined with a
            // literal `return null` (eager wrapping could nest once the
            // variable resolves to a nullable type), which understates a
            // generic body's return (`get`'s value-or-null is `V?`, not `V`).
            // Re-wrap here: a body with a null return is nullable. Consumers
            // collapse a nested `T??` to `T?` after instantiation (see
            // `brass_hir::collapse_nullable`).
            match common {
                Some(t) if collected.iter().any(|(r, _)| r.is_null()) => {
                    Some(match self.resolve(&t) {
                        resolved @ Type::Nullable(_) => resolved,
                        other => Type::Nullable(Box::new(other)),
                    })
                }
                other => other,
            }
        } else {
            None
        };
        // Only an escaping numeric origin or closure can receive a demand
        // from outside this body. Other results fix local negotiation entirely
        // from the effective inputs, so those bodies need no extra identity.
        if self.numeric.probing {
            let exports_origin = ret.is_none()
                && (self.numeric.result.is_some()
                    || result.as_ref().is_some_and(|ty| {
                        matches!(
                            self.resolve(ty),
                            Type::Int(_) | Type::Float(_) | Type::Fun(..)
                        )
                    }));
            self.leave_numeric_body(exports_origin);
        }
        result
    }

    /// Check every statement of a block in statement position.
    fn check_block(&mut self, b: &Block, scopes: &mut ScopeStack) {
        self.check_block_stmts(b, scopes);
    }

    /// The checker's one statement walker, behind both statement blocks
    /// ([`Self::check_block`]) and blocks in expression position
    /// ([`Self::check_block_expr`]), so guard narrowing, static divergence and
    /// return pruning mean the same thing in both. Returns the block's value:
    /// its trailing expression's type, `void` when it ends in a statement, or
    /// `Never` when it always leaves (see [`Self::check_block_expr`]).
    ///
    /// Statements after a statically-folded `if` whose taken arm always returns
    /// are UNREACHABLE (see [`Checker::static_divergence`]). They are still
    /// walked -- so the calls they make still reach monomorphization -- but their
    /// type errors are dropped, the same treatment the dead arm of such an `if`
    /// gets. This is what lets a generic body pick the arm that fits its
    /// instantiation and fall through for the others:
    ///
    /// ```text
    /// fun as_text(v) -> string {
    ///     if v._components { return v.to_string() }   // a Path: returns here
    ///     return v                                    // a string: unreachable above
    /// }
    /// ```
    ///
    /// A `bool` condition never folds, so ordinary control flow is unaffected:
    /// only a condition the type alone decides (a present member vs an absent
    /// one, a type test) can make a fall-through dead.
    pub(super) fn check_block_stmts(&mut self, b: &Block, scopes: &mut ScopeStack) -> Type {
        scopes.push(Scope::default());
        self.const_scopes.push(HashSet::default());
        // The unreachable statements contribute no `return`s either (their
        // values are collected into a discarded scratch frame), mirroring the
        // back end, which joins only the returns of reachable blocks.
        let mut unreachable = false;
        let mut last = Type::Void;
        let mut diverges = false;
        let bindings = binding_joins::BlockBindings::new(&b.stmts);
        for (index, s) in b.stmts.iter().enumerate() {
            let mark = self.errors.len();
            self.static_divergence = false;
            let value = self.discarded_walk(unreachable, |this| {
                if unreachable {
                    this.return_values.push(Vec::new());
                    let value = this.check_stmt(s, scopes);
                    this.return_values.pop();
                    value
                } else {
                    this.check_stmt(s, scopes)
                }
            });
            // A monomorphic closure binding's open numeric parameters take the
            // join of its direct applications' arguments in the rest of the
            // block, fixed before the first of them is checked.
            if bindings.after(index).is_some() {
                self.pin_closure_parameters(&bindings, index, scopes);
            }
            match s {
                Stmt::Expr(_) => {
                    diverges |= matches!(self.resolve(&value), Type::Never);
                    last = value;
                }
                Stmt::Return(..) | Stmt::Break(_) | Stmt::Continue(_) => {
                    diverges = true;
                    last = Type::Void;
                }
                _ => last = Type::Void,
            }
            if unreachable {
                self.errors.truncate(mark);
            } else {
                unreachable = self.static_divergence;
            }
        }
        self.static_divergence = false;
        self.const_scopes.pop();
        scopes.pop();
        if diverges { Type::Never } else { last }
    }

    /// Check a `return` against the active return context. The context is the
    /// top of `return_contexts`, pushed by `check_block_root` for a function or
    /// method body and by the closure checker for a closure body. Consulting
    /// the stack rather than a positionally-threaded parameter means a `return`
    /// nested inside an `if`/bare block/`match`-arm that is evaluated as an
    /// expression is still checked against the enclosing callable's declared
    /// type, and a `return` inside a closure is checked against the closure's
    /// own (inferred) context rather than the outer function.
    fn check_return(
        &mut self,
        value: Option<&Expr>,
        span: brass_parser::Span,
        scopes: &mut ScopeStack,
    ) {
        let returned = match self.return_contexts.last().cloned() {
            Some(ReturnContext::Explicit(want)) => match value {
                Some(e) => {
                    // A fallible return type (`-> T!`, or any `Result`) auto-wraps a
                    // bare value as `Ok { value }`: check it against the Ok payload.
                    // A `Result`-typed value flows whole. This mirrors the inferred
                    // fallible path.
                    let resolved = self.resolve(&want);
                    let result_return = match &resolved {
                        Type::Nullable(inner) if inner.is_result_type() => inner.as_ref(),
                        other => other,
                    };
                    if let Some((ok, _err)) = result_return.result_payloads()
                        && (self.is_anonymous_literal_into(e, ok) || matches!(e, Expr::Array(..)))
                    {
                        // A record literal returned as the Ok payload is
                        // built as the payload's declared record, and a
                        // bracket literal takes the payload's shape (rule 1
                        // of bracket literals: the annotation decides).
                        let ok = ok.clone();
                        self.check_expr_against(e, &ok, scopes)
                    } else if let Some((ok, _err)) = result_return.result_payloads() {
                        let ok = ok.clone();
                        // `return e` or `return e!` where the enclosing return
                        // is `T!` keys a reflective method called by `e` by the
                        // Ok payload `ok`. Set the channel narrowly for a
                        // direct call / `call!`.
                        if matches!(e, Expr::Call(..) | Expr::ErrorProp(..)) {
                            self.call_expected = Some(ok.clone());
                        }
                        let got = self.check_expr(e, scopes);
                        self.call_expected = None;
                        // A declared subtype of the return's Result also flows
                        // whole (the flow site coerces it). A null or an
                        // already-nullable Result belongs to the declared outer
                        // nullable layer rather than to the Result's Ok payload.
                        let got_res = self.resolve(&got);
                        let outer_nullable = matches!(resolved, Type::Nullable(_));
                        let nullable_result = matches!(
                            &got_res,
                            Type::Nullable(inner) if inner.is_result_type()
                        );
                        if outer_nullable && (got_res.is_null() || nullable_result) {
                            self.expect_expr_assignable(&got, &want, e);
                        } else {
                            let whole = got_res.is_result_type()
                                || matches!((&got_res, result_return), (Type::Sum(h), Type::Sum(w))
                                    if crate::structural::declares_sum_parent(self.program, h.id, w.id, 0));
                            if whole {
                                let flowed =
                                    self.link_forwarded_error(&got_res, result_return, e.span());
                                // A returned Result is one of the callable's
                                // error sources: when the flow fails because
                                // its Err payload has no join with the
                                // declared one, that is reported like every
                                // payload conflict.
                                let mark = self.errors.len();
                                self.expect_expr_assignable(&flowed, &want, e);
                                if self.errors.len() > mark {
                                    self.reword_returned_error_conflict(
                                        mark,
                                        &flowed,
                                        result_return,
                                        e.span(),
                                    );
                                }
                            } else {
                                self.expect_expr_assignable(&got, &ok, e);
                            }
                        }
                        got
                    } else {
                        self.check_expr_against(e, &want, scopes)
                    }
                }
                None => {
                    // A fallible return wraps a bare `return` exactly like a
                    // bare value: no value is a void payload, so `-> void!`
                    // accepts it as the Ok exit (and `-> int32!` reports the
                    // payload mismatch, not a mismatch against the whole
                    // `Result`).
                    let resolved = self.resolve(&want);
                    let result_return = match &resolved {
                        Type::Nullable(inner) if inner.is_result_type() => inner.as_ref(),
                        other => other,
                    };
                    if let Some((ok, _err)) = result_return.result_payloads() {
                        let ok = ok.clone();
                        self.expect_assignable(&Type::Void, &ok, span);
                    } else {
                        self.expect_assignable(&Type::Void, &want, span);
                    }
                    Type::Void
                }
            },
            // Inferred context (closure or unannotated function) or no context
            // (module top level): type the value but do not constrain it; the
            // return type is reconciled separately.
            _ => match value {
                Some(e) => self.check_discarded_expr(e, scopes),
                None => Type::Void,
            },
        };
        // Collect the resolved return type for the enclosing callable's inferred
        // return (see `return_values`); harmless for an explicit-return body, whose
        // collected values `check_block_root` discards.
        if self.numeric.probing && self.discarded_walks == 0 {
            let origin = value.and_then(|expr| self.numeric_source(expr));
            if let Some(frame) = self.numeric.returns.last_mut() {
                frame.push(origin);
            }
        }
        let resolved = self.resolve(&returned);
        if let Some(frame) = self.return_values.last_mut() {
            frame.push((resolved, span));
        }
        if let Some(e) = value {
            self.note_return_literal(span, e);
            self.return_value_spans.insert(span, e.span());
        }
    }

    /// Replace the flow errors reported since `mark` for the returned Result
    /// `got` with one incompatible-error-payloads report when its Err payload
    /// has no join with the declared Result's (`want`), so a conflicting
    /// error source reads the same whether it is returned or propagated with
    /// `!` (see `join_declared_error`). Any other flow failure stands.
    fn reword_returned_error_conflict(&mut self, mark: usize, got: &Type, want: &Type, span: Span) {
        let (Type::Sum(got_sum), Type::Sum(want_sum)) = (self.resolve(got), self.resolve(want))
        else {
            return;
        };
        let (Some(raised), Some(declared)) = (
            got_sum.substitution.get(brass_hir::types::RESULT_ERR_ERROR),
            want_sum
                .substitution
                .get(brass_hir::types::RESULT_ERR_ERROR),
        ) else {
            return;
        };
        let (raised, declared) = (self.resolve(raised), self.resolve(declared));
        if raised.is_unknown() || declared.is_unknown() {
            return;
        }
        let errors = self.errors.split_off(mark);
        if self.join_declared_error(&declared, &raised, "this `return` raises", span) {
            self.errors.extend(errors);
        }
    }

    /// Commit the return annotation's OPEN Err payload to a forwarded
    /// Result's. `T!` infers its Err from the body's error sources; a body
    /// whose only source is a forwarded callee Result (`return helper()`)
    /// names the type only at this return, and the ordinary assignability
    /// probe is deliberately non-committing, so the binding is made here.
    fn link_forwarded_error(&mut self, got: &Type, want: &Type, span: Span) -> Type {
        // The Err slot alone decides: an Err-only construction has no
        // `Ok.value` entry, so `result_payloads` (which demands both keys)
        // would miss it.
        let g_err = match got {
            Type::Sum(n) if n.is_result_type() => n
                .substitution
                .get(brass_hir::types::RESULT_ERR_ERROR)
                .cloned(),
            _ => None,
        };
        let Some(g_err) = g_err else {
            return got.clone();
        };
        let g_err = self.resolve(&g_err);
        if g_err.is_unknown() {
            return got.clone();
        }
        // A forwarded payload that is not the prelude Error is re-raised
        // wrapped into one at this return (MIR rebuilds the Err arm), so
        // every error a fallible body hands back has one shape. The flowed
        // type -- what the return is checked at -- carries the lifted slot.
        let lifted = crate::lift_err_payload(self.program, g_err.clone());
        self.record_lift_kind(span, lifted != g_err);
        let flowed = if lifted != g_err {
            self.record_lift_err(span);
            match got {
                Type::Sum(n) => {
                    let mut n = n.clone();
                    n.substitution
                        .insert(brass_hir::types::RESULT_ERR_ERROR, lifted.clone());
                    Type::Sum(n)
                }
                other => other.clone(),
            }
        } else {
            got.clone()
        };
        if let Some((_, w_err)) = want.result_payloads()
            && self.resolve(w_err).is_unknown()
        {
            let w_err = w_err.clone();
            let _ = self.solver.unify(&w_err, &lifted);
        }
        flowed
    }

    /// Check one statement; returns the value of an expression statement
    /// (`void` for any other statement), which a block in expression position
    /// yields when it is the last one.
    pub(super) fn check_stmt(&mut self, s: &Stmt, scopes: &mut ScopeStack) -> Type {
        // A `let` initializer only binds its value: a `!` there reads nothing
        // yet (reading the binding is what counts, see
        // `reject_error_only_binding_read`).
        let Stmt::Let {
            value: Some(value), ..
        } = s
        else {
            return self.check_stmt_inner(s, scopes);
        };
        let mut spans = Vec::new();
        crate::walk::discarded_value_spans(value, &mut spans);
        let added: Vec<Span> = spans
            .into_iter()
            .filter(|span| self.discarded_values.insert(*span))
            .collect();
        let ty = self.check_stmt_inner(s, scopes);
        for span in added {
            self.discarded_values.remove(&span);
        }
        ty
    }

    fn check_stmt_inner(&mut self, s: &Stmt, scopes: &mut ScopeStack) -> Type {
        let mut value_ty = Type::Void;
        match s {
            Stmt::Let {
                pat,
                ty,
                value,
                is_const,
                ..
            } => {
                let Some(value) = value else {
                    // `let x: T` without an initializer: the annotation alone
                    // types the binding; the definite-assignment pass rejects
                    // any read before the binding is fully assigned.
                    self.bind_uninit_let(pat, ty.as_ref(), scopes);
                    return Type::Void;
                };
                let binding_ty = if let Some(te) = ty {
                    match self.resolve_annotation_scoped(te, scopes) {
                        Ok(annotated) => {
                            let got = self.check_expr_against(value, &annotated, scopes);
                            // Pin an open constructor result to the annotation, so
                            // the back end seeds the concrete instance: `let m: SI =
                            // HashMap.new()` fixes the witness-free map's key/value
                            // from `SI` (its inferred fields would otherwise stay
                            // open and its slot array read as `never`). Same-nominal
                            // only, rolled back on a genuine mismatch (already
                            // reported by `check_expr_against`).
                            let g = self.resolve(&got);
                            let a = self.resolve(&annotated);
                            if same_nominal_instance(&g, &a) {
                                let snap = self.solver.snapshot();
                                if self.solver.unify(&got, &annotated).is_err() {
                                    self.solver.rollback(snap);
                                }
                            }
                            self.instantiate_annotated_type(&annotated, &got)
                        }
                        Err(message) => {
                            self.errors.push(TypeError {
                                message,
                                span: te.span(),
                            });
                            self.check_expr(value, scopes)
                        }
                    }
                } else {
                    // An unannotated `const` bound directly to a non-empty array
                    // literal is immutable, so the literal types as a
                    // fixed-length array; a `let` binding stays a growable
                    // slice. An annotation (above) always wins.
                    self.fixed_array_binding =
                        *is_const && matches!(value, Expr::Array(es, _) if !es.is_empty());
                    let t = self.check_expr(value, scopes);
                    self.fixed_array_binding = false;
                    t
                };
                // Binding a NAME to a `void` value is a mistake with no
                // representable value behind it -- classically a block-bodied
                // closure that forgot `return`, whose call site would otherwise
                // fail much later with an opaque unsupported-construct error.
                // A wildcard (`let _ = f()`) still discards a void result.
                if let Pattern::Binding(name, None, span) = pat
                    && matches!(self.resolve(&binding_ty), Type::Void)
                {
                    self.errors.push(TypeError {
                        message: format!(
                            "cannot bind `{name}` to a `void` value (a block-bodied \
                             closure or function returns `void` without an explicit \
                             `return`)"
                        ),
                        span: *span,
                    });
                }
                self.check_let_pattern_against(
                    &binding_ty,
                    pat,
                    value,
                    if *is_const { "const" } else { "let" },
                );
                // A generalizable closure binding (an unannotated,
                // never-reassigned name bound to a closure literal with an
                // unannotated parameter; `brass_hir::generalized_closure_bindings`)
                // is let-polymorphic: its type is generalized over the
                // variables the environment (the scopes before the name is
                // bound) does not mention.
                if let Pattern::Binding(_, None, span) = pat {
                    self.generalize_closure_binding(*span, &binding_ty, scopes);
                }
                if let Pattern::Binding(name, _, _) = pat {
                    scopes.last_mut().unwrap().numeric.remove(name);
                }
                let binding_ty = if self.numeric.active && ty.is_none() {
                    self.numeric_binding_type(pat, value, &binding_ty, scopes)
                } else {
                    binding_ty
                };
                if self.numeric_enabled {
                    self.note_numeric_binding_layout(pat, &binding_ty);
                }
                let numeric_origin = match pat {
                    Pattern::Binding(name, None, _) => scopes
                        .last()
                        .and_then(|scope| scope.numeric.get(name))
                        .copied(),
                    _ => None,
                };
                self.bind_pattern(pat, &binding_ty, scopes);
                if let (Pattern::Binding(name, None, _), Some(origin)) = (pat, numeric_origin) {
                    scopes
                        .last_mut()
                        .unwrap()
                        .numeric
                        .insert(name.clone(), origin);
                }
                if self.numeric_enabled
                    && !self.numeric.active
                    && ty.is_none()
                    && brass_typesys::NumericLiteral::of_expr(value).is_some()
                    && let Pattern::Binding(_, None, span) = pat
                {
                    self.record_typed(
                        brass_hir::TypedExprKind::NumericBinding,
                        *span,
                        binding_ty.clone(),
                        Constness::Unknown,
                    );
                }
                if *is_const {
                    self.record_expr_type_with(value, &binding_ty, Constness::Const);
                    self.bind_const_pattern(pat);
                }
            }
            Stmt::Assign {
                target,
                op,
                value,
                span,
            } => {
                // Rebinding a narrowed name stores into its DECLARED nullable
                // type; a possibly-null value ends the narrowing from here on.
                // A still-open value (an unannotated parameter in a generic
                // body's own pass) is left open rather than pinned to `T?`:
                // each instantiation's pass decides with the real type.
                if matches!(op, AssignOp::Eq)
                    && let Expr::Ident(name, _) = target
                    && let Some(declared) = self.narrowed_declared_type(scopes, name)
                {
                    self.record_expr_type(target, &declared);
                    let stored = self.check_expr_against(value, &declared, scopes);
                    if !self.resolve(&stored).is_unknown() {
                        self.constrain_stored_value(&stored, &declared);
                    }
                    self.after_rebinding(scopes, name, &stored);
                    return Type::Void;
                }
                let target_ty = self.check_place(target, scopes);
                if matches!(op, AssignOp::Eq) {
                    // A store into an array element whose type still carries an
                    // open inference variable commits the value into it (the way
                    // `push` does), so `arr[i] = v` pins an as-yet-unknown element
                    // -- including a record element with open fields (`_Entry<?,
                    // ?>`), whose key/value the stored value refines through the
                    // solver. A fully-concrete element keeps the ordinary
                    // bidirectional check (typed integer literals, structural
                    // compatibility).
                    let target_open = matches!(target, Expr::Index(..))
                        && !self.solver.free_vars(&self.resolve(&target_ty)).is_empty();
                    if target_open {
                        let value_ty = self.check_expr(value, scopes);
                        self.expect_element_assignable(&value_ty, &target_ty, value);
                    } else {
                        let value_ty = self.check_expr_against(value, &target_ty, scopes);
                        if self.numeric.probing {
                            self.numeric_store(target, &value_ty, Some(value), scopes);
                        }
                        self.constrain_stored_value(&value_ty, &target_ty);
                    }
                } else {
                    // `x op= e` is `x = x op e`: the operator rule types the pair
                    // (a literal `e` adapts to `x` when it fits, so `u += 1`
                    // stays at `u`'s type), and the combined result is stored
                    // back, so it must flow into the target's type: `int64 +=
                    // int32` widens the operand, but `int32 += float64` would
                    // need a silent float -> int truncation and is rejected.
                    let value_ty = self.check_expr(value, scopes);
                    let result = self.check_binary_expr(
                        assign_binop(*op),
                        target,
                        &target_ty,
                        value,
                        &value_ty,
                        *span,
                    );
                    if self.numeric.probing {
                        self.numeric_store(target, &result, None, scopes);
                    }
                    self.expect_assignable(&result, &target_ty, *span);
                }
            }
            Stmt::Expr(e) => {
                // The value of an expression statement is discarded unless it
                // is the trailing value of a block in expression position.
                value_ty = if self.block_value_tail == Some(e.span()) {
                    let expect = self.tail_expectation.take();
                    self.check_branch_value(e, expect.as_ref(), scopes)
                } else {
                    self.check_statement_expr(e, scopes)
                };
            }
            Stmt::While { cond, body, .. } => {
                // `while x { .. }` proves `x` non-null for the body, like the
                // then-arm of `if x`: the condition is re-tested before every
                // iteration.
                self.check_loop(scopes, |this, scopes| {
                    this.check_condition(cond, scopes);
                    scopes.push(Scope::default());
                    this.const_scopes.push(HashSet::default());
                    this.apply_truthy_narrowing(cond, scopes);
                    this.check_block(body, scopes);
                    this.const_scopes.pop();
                    scopes.pop();
                });
            }
            Stmt::For {
                pat, iter, body, ..
            } => {
                if brass_hir::fields_loop_target(s).is_some() {
                    self.check_construct_binding("fields", iter.span(), scopes);
                    self.check_fields_loop(s, scopes);
                    return Type::Void;
                }
                let iter_ty = self.check_expr(iter, scopes);
                // Iterating sees through reference/mutability wrappers and binds the
                // loop variable to the element of the same kind: over `ref(mut(T[]))`
                // each element is a `ref(mut(T))`, so mutating it writes through.
                let item_ty = self.for_element(&iter_ty).unwrap_or_else(|| {
                    self.errors.push(TypeError {
                        message: format!(
                            "cannot iterate over `{}`",
                            self.resolve(&iter_ty).display()
                        ),
                        span: iter.span(),
                    });
                    self.fresh_unknown()
                });
                // Check the loop variable's pattern against the element type, so a
                // destructuring of the wrong arity is a diagnostic here rather than
                // an out-of-bounds tuple read in the back end.
                self.check_pattern_against(&item_ty, pat);
                self.check_irrefutable_pattern(&item_ty, pat, None, "for");
                self.check_loop(scopes, |this, scopes| {
                    scopes.push(Scope::default());
                    this.const_scopes.push(HashSet::default());
                    this.bind_pattern(pat, &item_ty, scopes);
                    this.check_block(body, scopes);
                    this.const_scopes.pop();
                    scopes.pop();
                });
            }
            Stmt::Return(value, span) => self.check_return(value.as_ref(), *span, scopes),
            Stmt::Break(_) | Stmt::Continue(_) => {}
        }
        self.apply_guard_narrowing(s, scopes);
        value_ty
    }

    /// Resolve a local-binding annotation with the value scope in hand, so a
    /// `typeof(v)` node ties the binding to `v`'s inferred type (`let x:
    /// typeof(v)` gives x the same type as v). Nullable, array, fallible,
    /// passing-mode, function and tuple wrappers around a `typeof` recurse; any other
    /// annotation delegates to `resolve_type`. `v` is type-checked (needed to
    /// know its type) but never lowered.
    fn resolve_annotation_scoped(
        &mut self,
        te: &TypeExpr,
        scopes: &mut ScopeStack,
    ) -> Result<Type, String> {
        let resolved = self.resolve_annotation_scoped_inner(te, scopes)?;
        // A `typeof`-bearing annotation is not recoverable by MIR's scope-free
        // resolver, so record the resolved type for the back end to seed the
        // binding's slot (needed when the initializer -- e.g. `null` -- does not
        // itself carry the type). Typed observations carry the instance tag
        // through memo replay and the InstanceChannel of slot seeds; the
        // span-only channel holds just the type shared by all instances.
        if contains_typeof(te) {
            let span = te.span();
            self.record_typed(
                brass_hir::TypedExprKind::TypeOfAnnotation,
                span,
                resolved.clone(),
                Constness::Unknown,
            );
            self.record_typeof_type(span, &resolved);
        }
        Ok(resolved)
    }

    fn resolve_annotation_scoped_inner(
        &mut self,
        te: &TypeExpr,
        scopes: &mut ScopeStack,
    ) -> Result<Type, String> {
        match te {
            TypeExpr::TypeOf(e, _) => Ok(self.check_expr(e, scopes)),
            TypeExpr::Fun(params, ret, _) => {
                let params = params
                    .iter()
                    .map(|param| self.resolve_annotation_scoped_inner(param, scopes))
                    .collect::<Result<Vec<_>, _>>()?;
                let ret = self.resolve_annotation_scoped_inner(ret, scopes)?;
                Ok(Type::Fun(params, Box::new(ret)))
            }
            TypeExpr::Nullable(inner, _) => Ok(Type::nullable(
                self.resolve_annotation_scoped_inner(inner, scopes)?,
            )),
            TypeExpr::Array(inner, Some(n), _) => Ok(Type::Array(
                Box::new(self.resolve_annotation_scoped_inner(inner, scopes)?),
                *n,
            )),
            TypeExpr::Array(inner, None, _) => Ok(Type::Slice(Box::new(
                self.resolve_annotation_scoped_inner(inner, scopes)?,
            ))),
            TypeExpr::Fallible(inner, span) => {
                let ok = self.resolve_annotation_scoped_inner(inner, scopes)?;
                let err = self.fresh_unknown();
                Ok(self.scoped_result(ok, err, *span))
            }
            TypeExpr::Mut(inner, _) => Ok(Type::Mut(Box::new(
                self.resolve_annotation_scoped_inner(inner, scopes)?,
            ))),
            TypeExpr::Ref(inner, _) => Ok(Type::Ref(Box::new(
                self.resolve_annotation_scoped_inner(inner, scopes)?,
            ))),
            TypeExpr::Tuple(elems, _) => {
                let mut ts = Vec::with_capacity(elems.len());
                for e in elems {
                    ts.push(self.resolve_annotation_scoped_inner(e, scopes)?);
                }
                Ok(Type::Tuple(ts))
            }
            // Every other annotation goes to the ordinary scope-free resolver,
            // where a `typeof` nested in an anonymous-record or
            // refinement type is an open variable not tied to its operand.
            _ => self.resolve_type(te),
        }
    }

    /// Bind an uninitialized `let x: T`: the annotation is the binding's type.
    /// Only a single-name binding makes sense (there is no value to
    /// destructure); the definite-assignment pass enforces write-before-read.
    fn bind_uninit_let(&mut self, pat: &Pattern, ty: Option<&TypeExpr>, scopes: &mut ScopeStack) {
        // The parser only omits the initializer when an annotation is present.
        let Some(te) = ty else { return };
        let binding_ty = match self.resolve_annotation_scoped(te, scopes) {
            Ok(t) => t,
            Err(message) => {
                self.errors.push(TypeError {
                    message,
                    span: te.span(),
                });
                return;
            }
        };
        if !matches!(pat, Pattern::Binding(_, None, _)) {
            self.errors.push(TypeError {
                message: "an uninitialized `let` must bind a single name".to_string(),
                span: te.span(),
            });
            return;
        }
        self.check_irrefutable_pattern(&binding_ty, pat, None, "let");
        self.bind_pattern(pat, &binding_ty, scopes);
    }

    /// Check a `for f in fields(x)` loop: `x` must be a record; the body is
    /// expanded and checked once per field (declaration order for a nominal
    /// record, canonical key order for an anonymous one), with the loop
    /// variable decayed to the field name and `v[f]` to the field projection
    /// (see `brass_hir::expand`). The field list is recorded for MIR
    /// lowering, which unrolls the identical copies.
    fn check_fields_loop(&mut self, s: &Stmt, scopes: &mut ScopeStack) {
        if let Stmt::For {
            pat: pat @ Pattern::Binding(_, Some(_), _),
            ..
        } = s
        {
            // Reflection yields field names, not variants. Validate before
            // expansion can mistake the qualified head for a loop binding.
            self.check_pattern_against(&Type::Str, pat);
            return;
        }
        if let Stmt::For { pat, .. } = s {
            self.check_irrefutable_pattern(&Type::Str, pat, None, "for");
        }
        let Some((var, arg, body)) = brass_hir::fields_loop_target(s) else {
            return;
        };
        let arg_ty = self.check_expr(arg, scopes);
        let resolved = self.resolve(&arg_ty);
        let (type_name, field_names) = match peel_modes(&resolved) {
            // An operand whose type this pass leaves open -- an unannotated
            // parameter in the definitional pass of a generic body -- is a
            // requirement on each instance, like any other member access on
            // it: every call site's elaboration checks the loop at its own
            // record type and records that instance's field list.
            Type::Unknown(_) => return,
            Type::Record(n) if n.id == brass_hir::STRUCTURAL_RECORD_ID => (
                brass_hir::STRUCTURAL_RECORD_NAME.to_string(),
                n.substitution.iter().map(|(k, _)| k.to_string()).collect(),
            ),
            Type::Record(n) => {
                let Some(info) = self.program.type_by_id(n.id) else {
                    self.errors.push(TypeError {
                        message: format!(
                            "`fields(..)` requires a record value, got `{}`",
                            resolved.display()
                        ),
                        span: arg.span(),
                    });
                    return;
                };
                let TypeKind::Record { fields, .. } = &info.kind else {
                    self.errors.push(TypeError {
                        message: format!(
                            "`fields(..)` requires a record value, got `{}`",
                            resolved.display()
                        ),
                        span: arg.span(),
                    });
                    return;
                };
                (
                    info.name.clone(),
                    fields.iter().map(|f| f.name.clone()).collect::<Vec<_>>(),
                )
            }
            other => {
                self.errors.push(TypeError {
                    message: format!(
                        "`fields(..)` requires a record value, got `{}`",
                        other.display()
                    ),
                    span: arg.span(),
                });
                return;
            }
        };
        // Each callable instance records the exact expansion checked here.
        // MIR can share an expansion only while every instance agrees.
        if !self.record_fields_loop(s.span(), field_names.clone()) {
            return;
        }
        for (i, field) in field_names.iter().enumerate() {
            let expanded = brass_hir::expand_fields_body(body, var, field, i);
            let err_start = self.errors.len();
            self.check_block(&expanded, scopes);
            // Copies carry shifted spans (so span-keyed sidecars stay distinct
            // per copy); surface diagnostics at the source position, naming
            // the field whose copy failed.
            for e in &mut self.errors[err_start..] {
                e.span = brass_hir::unshift_span(e.span);
                e.message = format!(
                    "{} (while expanding field `{field}` of `{type_name}`)",
                    e.message
                );
            }
        }
    }
}
