//! Call typing: dispatching a call expression to free functions,
//! builtin and primitive methods, user methods (keyed, structural, or
//! by receiver), callable values, and static type-qualified calls;
//! plus argument checking against signatures, arity validation, and
//! re-attribution of argument errors to the call site.

mod constructs;

use super::*;

/// A record type declaring the method a structural (anonymous) receiver asked
/// for, as seen from the call's module: whether the type is visible there and
/// which of its fields the value fails to satisfy. Shared by candidate
/// selection and the resolution-failure diagnostics.
struct StructuralMethodType {
    name: String,
    symbol: String,
    /// Declared in or imported into the current module (builtins and the
    /// public std prelude count). Only visible types dispatch; a satisfied
    /// but invisible type is reported as a missing import.
    visible: bool,
    /// Members of the declaring type the value does not provide; empty when
    /// the value satisfies the type.
    unsatisfied: Vec<String>,
}

impl<'a> Checker<'a> {
    /// Type the call `callee(args)` at `span` and return its result type. A
    /// bare name resolves in this order: the language constructs,
    /// a builtin the call reaches, a bound value, a free function
    /// visible here (its body re-elaborated at the arguments). `recv.m(..)`
    /// resolves as a static call when `recv` names a type, else as a method,
    /// stdlib primitive method or function-typed field of the receiver's
    /// type. Any other callee is applied as a function value.
    pub(super) fn check_call(
        &mut self,
        callee: &Expr,
        args: &[Arg],
        span: brass_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        if !self.numeric_enabled {
            return self.check_call_inner(callee, args, span, scopes);
        }
        let saved = self.numeric.result.take();
        if self.numeric.active {
            self.numeric.calls.push(span);
        }
        let ty = self.check_call_inner(callee, args, span, scopes);
        let origin = self.numeric.result.take();
        if self.numeric.active {
            self.numeric.calls.pop();
        }
        self.numeric.result = origin;
        self.note_numeric_call(span);
        self.numeric.result = saved;
        ty
    }

    fn check_call_inner(
        &mut self,
        callee: &Expr,
        args: &[Arg],
        span: Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        // Consume the caller's expectation (a keyed `-> infer!` method reads it);
        // taking it here keeps an argument's own calls from reusing it.
        let call_expected = self.call_expected.take();
        if let Expr::Ident(name, _) = callee {
            if let Some(ret) =
                self.check_construct_call(name, args, span, scopes, call_expected.as_ref())
            {
                return ret;
            }
            if let Some(ret) = self.builtin_function_type(name, args, span, scopes) {
                return ret;
            }
            // A local binding (e.g. a closure parameter) shadows a same-named
            // global function, matching codegen's resolution order.
            if let Some(local) = self.lookup(scopes, name) {
                // A generalized closure is applied at its own instance.
                let local = self.instantiate_closure_scheme(local);
                // Record the callee's type so hover can recover it. Applying it
                // below constrains an unknown callee to a function type, and the
                // final zonking pass then resolves this recorded type through it,
                // so `fun apply(f, x) { f(x) }` shows `f` as `(U) -> V`.
                let closure_body = match &local {
                    Type::Fun(params, ret) if self.numeric_enabled => {
                        self.saved_closure_body(params, ret)
                    }
                    _ => None,
                };
                let ret = self.check_callable_value(name, local.clone(), args, span, scopes);
                if let Some(body) = closure_body
                    && let Expr::Closure(_, body, _) = &body.expr
                {
                    self.record_numeric_call(
                        callee.span(),
                        self.numeric_layout_for(body.span()),
                        self.current_instance(),
                    );
                }
                let effective = match self.resolve(&local) {
                    Type::Fun(params, _) => Type::Fun(params, Box::new(ret.clone())),
                    other => other,
                };
                self.record_expr_type(callee, &effective);
                self.invalidate_narrowed_after_call(scopes);
                return ret;
            }
            // Only a function visible from the current module resolves here; a
            // function defined in another, non-imported module is invisible and
            // falls through to the unknown-name path below. The
            // lookup is module-aware so a name defined in several modules
            // resolves to this module's own or imported definition.
            if let Some(info) = self.lookup_function(name) {
                let decl = info.decl.clone();
                let signature_params = info.signature.params.clone();
                let declared_ret = info.signature.ret_ty.clone();
                let symbol = info.symbol.clone();
                let module = info.module.clone();
                self.check_arg_count_range(name, &signature_params, args.len(), span);
                let arg_types = self.check_signature_args_collect(&signature_params, args, scopes);
                let fallback_ret = declared_ret
                    .clone()
                    .or_else(|| self.function_returns.get(&symbol).cloned())
                    .unwrap_or_else(|| self.fresh_unknown());
                // An ANONYMOUS structural argument to a row-covered eligible
                // parameter is checked against the callee's derived row HERE, at
                // the value's own span: presence of every Required field and its
                // Forced type. This, not the body re-elaboration, is the error
                // source for these arguments -- on a row failure the body is not
                // re-elaborated at all (the call is already known bad; interior
                // spans would only duplicate the value-site report). A clean row
                // check records the argument span so lowering may convert the
                // argument into the parameter's view, and the body below is
                // elaborated at that view: the back ends compile the callee for
                // the view, so the checker must see exactly its field types.
                let Some(elaboration_types) =
                    self.check_args_against_rows(name, &symbol, args, &arg_types)
                else {
                    self.invalidate_narrowed_after_call(scopes);
                    return fallback_ret;
                };
                // The lazy profile types a call from the signature alone when
                // re-elaborating the body could not tell it more (see
                // `Checker::lazy_profile`): the entry's gate then costs the
                // entry's own body, not its call tree. Never for a callee
                // that can reach a keyed (`-> infer!`) call -- that call must
                // be SEEN here, or it could first be reported after execution
                // began, too late to specialize (see `Checker::keyed_tainted`).
                //
                // Only for a callee that GETS a dedicated pass and is fully
                // annotated: such a body is instantiation-independent and its
                // own pass records its channels. A SEEDED (context) body has
                // no dedicated pass -- this call-site elaboration is a source
                // of its channel entries -- so seeded calls keep elaborating.
                // A record argument of another declaration than its
                // parameter's annotation (structural subtyping) instantiates
                // the callee at the argument's type, so that body is checked
                // here at it.
                let skip_elaboration = self.lazy_profile
                    && !self.keyed_tainted.contains(&symbol)
                    && !self.seeded_module(&module)
                    && declared_ret.as_ref().is_some_and(brass_hir::is_fully_known)
                    && signature_params.iter().all(|p| {
                        p.resolved_ty
                            .as_ref()
                            .is_some_and(|t| brass_hir::is_fully_known(brass_hir::peel_modes(t)))
                    })
                    && signature_params.iter().zip(&arg_types).all(|(p, arg)| {
                        p.resolved_ty
                            .as_ref()
                            .is_none_or(|t| !self.param_instance_follows_argument(t, arg))
                    });
                if skip_elaboration {
                    self.invalidate_narrowed_after_call(scopes);
                    return fallback_ret;
                }
                let before = self.errors.len();
                let ret = self.instantiate_function_call(
                    &symbol,
                    &module,
                    &signature_params,
                    &decl.body,
                    declared_ret,
                    fallback_ret,
                    &elaboration_types,
                    span,
                );
                // A body re-elaboration failure caused by an ANONYMOUS argument
                // is reported at the value, not inside the callee: the body
                // states the parameter's constraints, the caller's value is
                // where the mismatch lives. Only a single structural argument
                // attributes unambiguously; other calls keep the body spans.
                if self.errors.len() > before {
                    let structural: Vec<usize> = arg_types
                        .iter()
                        .enumerate()
                        .filter(|(_, t)| {
                            matches!(
                                brass_hir::peel_modes(&self.resolve(t)),
                                Type::Record(n) if n.id == brass_hir::STRUCTURAL_RECORD_ID
                            )
                        })
                        .map(|(i, _)| i)
                        .collect();
                    if let [idx] = structural.as_slice()
                        && let Some(arg) = args.get(*idx)
                    {
                        self.reattribute_errors(
                            before,
                            &format!("this value does not fit `{name}`'s parameter"),
                            arg.expr.span(),
                        );
                    }
                }
                // User code ran conceptually: a narrowed global (or a local a
                // closure of this body assigns) may have been re-nulled.
                self.invalidate_narrowed_after_call(scopes);
                return ret;
            }
            // The callee is a bare identifier that is not `error`, a builtin, a
            // local value, or a known free function. A runtime builtin (e.g.
            // `println` when the stdlib is not loaded) or a type word falls
            // through to the callee-value path below; any other name is
            // undeclared and reported here rather than collapsing to a fresh
            // unknown.
            if !self.is_resolvable_free_name(name) && !self.is_type_word(name) {
                // A function that exists but is not visible here gets a
                // pointed hint: an import for a public name; privacy for a
                // `_` name (which cannot be imported, so no import hint).
                let message = match self.program.functions.get(name) {
                    Some(f) if !f.module.is_empty() && name.starts_with('_') => {
                        format!("`{name}` is private to module `{}`", f.module.join("."))
                    }
                    Some(f) if !f.module.is_empty() => format!(
                        "`{name}` is defined in module `{}` but not imported here",
                        f.module.join(".")
                    ),
                    _ => format!("unknown function `{name}`"),
                };
                self.errors.push(TypeError { message, span });
                for a in args {
                    self.check_expr(&a.expr, scopes);
                }
                return self.fresh_unknown();
            }
        }
        if let Expr::Field(base, method, _) = callee
            && !callee.span().is_parenthesized()
        {
            if let Expr::Call(c, _, tspan) = &**base
                && matches!(&**c, Expr::Ident(n, _) if n == "typeof")
            {
                self.check_construct_binding("typeof", *tspan, scopes);
            }
            // `typeof(<compound>).method(..)` -- a literal, a call, an element
            // read: the operand is typed (and runs for its effects) and its
            // static type is the receiver, exactly as for `typeof(v)`.
            if let Expr::Call(c, cargs, tspan) = &**base
                && matches!(&**c, Expr::Ident(n, _) if n == "typeof")
                && let [operand] = cargs.as_slice()
                && !matches!(operand.expr, Expr::Ident(..) | Expr::SelfExpr(_))
            {
                let operand_ty = self.check_expr(&operand.expr, scopes);
                if let Some(qualifier) = self.type_qualifier(&operand_ty) {
                    self.record_type_name(*tspan, qualifier.clone());
                    let ret = self.check_static_call(&qualifier, method, args, span, scopes);
                    self.invalidate_narrowed_after_call(scopes);
                    return ret;
                }
                for a in args {
                    self.check_expr(&a.expr, scopes);
                }
                return self.fresh_unknown();
            }
            if let Some(qualifier) = self.static_call_qualifier(base, method, scopes) {
                // A `typeof(v)` qualifier resolves to v's type NAME; record it at
                // the inner `typeof(v)` span so MIR routes the static call. The
                // channel is keyed by span while MIR shares one body across a
                // generic's instantiations, so a qualifier that resolves to a
                // DIFFERENT type in another instantiation cannot be represented:
                // reject it here rather than let the last-checked name silently
                // dispatch every instance's call.
                if let Expr::Call(c, cargs, tspan) = &**base
                    && matches!(&**c, Expr::Ident(n, _) if n == "typeof")
                {
                    for a in cargs {
                        self.check_expr(&a.expr, scopes);
                    }
                    self.record_type_name(*tspan, qualifier.clone());
                }
                let ret = self.check_static_call(&qualifier, method, args, span, scopes);
                // A REFINEMENT-alias qualifier carries pinned slot types
                // (`type Names = Stack { item: string }`); flow them into the
                // call's result so `Names.new()` builds the pinned instance,
                // exactly as the annotated form `let s: Names = Stack.new()`
                // does. A plain alias (empty substitution) pins nothing.
                if let Expr::Ident(alias_name, _) = &**base
                    && self.lookup(scopes, alias_name).is_none()
                    && let Some(alias_ty) = self.resolve_alias(alias_name)
                    && matches!(&alias_ty, Type::Record(n) if !n.substitution.is_empty())
                    && self.can_unify(&ret, &alias_ty)
                {
                    let _ = self.solver.unify(&ret, &alias_ty);
                }
                self.invalidate_narrowed_after_call(scopes);
                return ret;
            }
            // `typeof(v).method(..)` whose `v` is still open (a generic body's
            // definitional pass) names no type yet; every instance resolves
            // the static call at its own type. It is not a method call on the
            // type-name string `typeof(v)` decays to elsewhere.
            if let Expr::Call(c, cargs, _) = &**base
                && matches!(&**c, Expr::Ident(n, _) if n == "typeof")
            {
                for a in cargs.iter().chain(args) {
                    self.check_expr(&a.expr, scopes);
                }
                return self.fresh_unknown();
            }
            let recv_ty = self.check_expr(base, scopes);
            let resolved_receiver = self.resolve(&recv_ty);
            self.check_const_method_call(span, method, &resolved_receiver);
            self.record_typed(
                brass_hir::TypedExprKind::MethodReceiver,
                span,
                resolved_receiver,
                Constness::Unknown,
            );
            if let Some(ret) = self.builtin_method_type(&recv_ty, method, args, scopes, span) {
                self.record_call_kind(span, None);
                return ret;
            }
            if let Type::Nullable(_) = self.resolve_head(&recv_ty) {
                self.report_nullable_use(base.span());
            }
            // A reflective `-> infer!` method is keyed by the caller's
            // expectation: its result type is fixed per call site, and the
            // driver generates a concrete specialization per key (this call is
            // rewritten to it). The template body is not elaborated here.
            if let Some(methods) = self.methods_for_type(&recv_ty, method) {
                self.record_call_kind(span, None);
                if methods
                    .first()
                    .is_some_and(|m| brass_hir::keyed_return(m.method.ret.as_ref()))
                {
                    return self.check_keyed_method_call(
                        &recv_ty,
                        method,
                        args,
                        span,
                        call_expected.as_ref(),
                        scopes,
                    );
                }
                return self
                    .check_methods_call(methods, &recv_ty, method, args, span, None, scopes);
            }
            // A stdlib method on a primitive/array receiver (`fun string.split`,
            // `fun infer[].map`): dispatched by the receiver's class. There is no
            // UFCS fallback -- a free function is not callable through `recv.f()`.
            if let Some(ret) =
                self.check_primitive_method_call(&recv_ty, method, args, span, scopes)
            {
                self.record_call_kind(span, None);
                // Stdlib primitive methods are user-defined Brass code.
                self.invalidate_narrowed_after_call(scopes);
                return ret;
            }
            // The missing-method diagnostics below look through mode wrappers so
            // a `ref(mut(T))` receiver is reported against `T`.
            let peeled_recv = brass_hir::peel_modes(&self.resolve(&recv_ty)).clone();
            if let Type::Record(record) = &peeled_recv {
                // A function-typed FIELD is callable through the same syntax (a
                // method of the same name takes precedence, resolved above):
                // `a.func(4)` calls the closure the field holds.
                if let Some(fty) = self.field_value_type(record, method) {
                    let resolved = self.resolve(&fty);
                    // An interface-style member takes the enclosing type as its
                    // FIRST parameter (`b: (Self) -> string`); calling it as
                    // `a.b(..)` binds the receiver to that parameter
                    // implicitly, like a method call -- so a protocol record's
                    // members are callable through a value annotated with the
                    // protocol, and each instantiation dispatches to the
                    // concrete type's own method.
                    if let Type::Fun(params, ret) = &resolved
                        && params.len() == args.len() + 1
                        && params.first().is_some_and(|first| {
                            let first = self.resolve(first);
                            // The declaration may keep the receiver parameter
                            // as the abstract `Self` or resolve it to the
                            // enclosing nominal; both bind the receiver.
                            matches!(first, Type::SelfType)
                                || crate::structural::types_compatible(
                                    self.program,
                                    &peeled_recv,
                                    &first,
                                )
                        })
                    {
                        // Provided by a method of the receiver's concrete type:
                        // dispatched as a method call.
                        self.record_call_kind(span, None);
                        let (params, ret) = (params.clone(), (**ret).clone());
                        self.record_expr_type(callee, &fty);
                        for (a, want) in args.iter().zip(params[1..].iter()) {
                            self.check_expr_against(&a.expr, want, scopes);
                        }
                        self.invalidate_narrowed_after_call(scopes);
                        return ret;
                    }
                    if matches!(resolved, Type::Fun(..) | Type::Unknown(_)) {
                        // The receiver's identity as a type-test pattern: its
                        // nominal (any instance), or for an anonymous record
                        // any record with this field.
                        let pattern = if record.id == brass_hir::STRUCTURAL_RECORD_ID {
                            brass_hir::structural_record(vec![(
                                method.to_string(),
                                Type::Unknown(brass_hir::INFER_VAR),
                            )])
                        } else {
                            Type::Record(NominalType::new(record.id, record.name()))
                        };
                        self.record_call_kind(span, Some(pattern));
                        self.record_expr_type(callee, &fty);
                        let ret = self.apply_callable(Some(method), fty, args, span, scopes);
                        self.invalidate_narrowed_after_call(scopes);
                        return ret;
                    }
                    self.errors.push(TypeError {
                        message: format!(
                            "field `{method}` of `{record}` has type `{}` and is not callable",
                            resolved.display()
                        ),
                        span,
                    });
                    for a in args {
                        self.check_expr(&a.expr, scopes);
                    }
                    return self.fresh_unknown();
                }
                // A STRUCTURAL (anonymous) receiver resolves a method by
                // satisfaction: the unique in-scope record type declaring the
                // method whose fields the value provides dispatches without an
                // annotation. Several satisfied candidates are ambiguous, and a
                // near-miss (the method exists but the value lacks a field) is
                // reported AT THE VALUE with the missing constraint -- the
                // callee's requirements are known here.
                if record.id == brass_hir::STRUCTURAL_RECORD_ID {
                    let candidates = self.structural_method_candidates(record, method);
                    match candidates.as_slice() {
                        [(_, symbol)] => {
                            let nominal = self
                                .program
                                .types
                                .get(symbol)
                                .map(|info| info.type_ref())
                                .unwrap_or_else(|| Type::Record(record.clone()));
                            if let Some(methods) = self.methods_for_type(&nominal, method) {
                                let methods = methods
                                    .into_iter()
                                    .map(|m| {
                                        apply_method_substitution(m, &record.substitution, method)
                                    })
                                    .collect();
                                return self.check_methods_call(
                                    methods,
                                    &recv_ty,
                                    method,
                                    args,
                                    span,
                                    Some(base.span()),
                                    scopes,
                                );
                            }
                        }
                        [] => {
                            // Name a near-miss when one exists: which in-scope
                            // type declares the method, and which fields the
                            // value is missing for it.
                            if let Some(msg) = self.structural_near_miss(record, method) {
                                self.errors.push(TypeError {
                                    message: msg,
                                    span: base.span(),
                                });
                                for a in args {
                                    self.check_expr(&a.expr, scopes);
                                }
                                return self.fresh_unknown();
                            }
                        }
                        many => {
                            let names: Vec<&str> = many.iter().map(|(n, _)| n.as_str()).collect();
                            self.errors.push(TypeError {
                                message: format!(
                                    "ambiguous method call: the anonymous structure \
                                     satisfies `{}`, which all declare `{method}`; \
                                     annotate the value with one of them",
                                    names.join("`, `")
                                ),
                                span: base.span(),
                            });
                            for a in args {
                                self.check_expr(&a.expr, scopes);
                            }
                            return self.fresh_unknown();
                        }
                    }
                }
                self.errors.push(TypeError {
                    message: format!("`{record}` has no method `{method}`"),
                    span,
                });
                for a in args {
                    self.check_expr(&a.expr, scopes);
                }
                return self.fresh_unknown();
            }
            if let Type::Sum(sum) = &peeled_recv {
                self.errors.push(TypeError {
                    message: format!("`{sum}` has no common method `{method}`"),
                    span,
                });
                for a in args {
                    self.check_expr(&a.expr, scopes);
                }
                return self.fresh_unknown();
            }
            // A known receiver head determines method availability even when
            // its element or parameter types are still open.
            let resolved = peeled_recv;
            if !matches!(resolved, Type::Unknown(_)) {
                self.errors.push(TypeError {
                    message: format!("`{}` has no method `{method}`", resolved.display()),
                    span,
                });
                for a in args {
                    self.check_expr(&a.expr, scopes);
                }
                return self.fresh_unknown();
            }
            // No method resolves on this receiver here. An open receiver (an
            // inference variable) names no type yet: each instantiation of a
            // generic body re-elaborates the call at its concrete receiver, and
            // a `HasMethod` shape is recorded so a closure like
            // `(x) -> x.speak()` rejects an `int32` argument at its
            // application. The arguments are checked; the result stays open.
            if let Type::Unknown(_) = resolved {
                self.record_shape(&recv_ty, ShapeConstraint::HasMethod(method.to_string()));
            }
            for a in args {
                self.check_expr(&a.expr, scopes);
            }
            return self.fresh_unknown();
        }
        if callee.span().is_parenthesized()
            && let Expr::Field(base, method, _) = callee
        {
            let is_method = if let Some(qualifier) = self.static_qualifier(base, scopes) {
                self.method_for_qualifier(&qualifier, method).is_some()
                    || self.primitive_static_type(&qualifier, method).is_some()
                    || (method == "from" && self.record_head_id(&qualifier).is_some())
            } else {
                let recv_ty = self.check_expr(base, scopes);
                let resolved = self.resolve(&recv_ty);
                self.program
                    .member_presence(brass_hir::peel_modes(&resolved), method)
                    == Some(true)
            };
            if is_method {
                let receiver = match &**base {
                    Expr::Ident(name, _) => name.as_str(),
                    Expr::SelfExpr(_) => "self",
                    _ => "receiver",
                };
                self.errors.push(TypeError {
                    message: format!(
                        "`{receiver}.{method}` is a method; call it as `{receiver}.{method}(...)`"
                    ),
                    span: callee.span().ungrouped(),
                });
                for arg in args {
                    self.check_expr(&arg.expr, scopes);
                }
                return self.fresh_unknown();
            }
        }
        let callee_ty = self.check_expr(callee, scopes);
        let name = match callee {
            Expr::Ident(name, _) => Some(name.as_str()),
            _ => None,
        };
        let ret = self.apply_callable(name, callee_ty, args, span, scopes);
        self.invalidate_narrowed_after_call(scopes);
        ret
    }

    /// Type-check a call `recv.m(args)` to a stdlib method implemented on a
    /// primitive/array receiver with `fun T.m(self, ...)`. The receiver's class
    /// (`Type::primitive_class`) keys the method in `primitive_methods`; the body
    /// is an ordinary function whose first parameter is the receiver. Returns
    /// `None` if the receiver type carries no such method.
    fn check_primitive_method_call(
        &mut self,
        recv_ty: &Type,
        method: &str,
        args: &[Arg],
        span: brass_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        // Mode wrappers are peeled so a `ref(string)` / `mut(T[])` receiver still
        // dispatches to the stdlib primitive method of the underlying class.
        let class = brass_hir::peel_modes(&self.resolve(recv_ty)).primitive_class()?;
        let symbol = self
            .program
            .primitive_methods
            .get(&(class.to_string(), method.to_string()))?;
        let info = self.program.functions.get(symbol)?;
        let func = ReceiverCall::from_fun(info);
        Some(self.check_receiver_call(recv_ty, &func, method, args, span, scopes))
    }

    /// Shared core of a call whose first parameter is filled by the receiver:
    /// check argument count and types (the receiver against the first parameter,
    /// the call's arguments against the rest) and instantiate the body for the
    /// resolved argument tuple, returning the inferred result type.
    fn check_receiver_call(
        &mut self,
        recv_ty: &Type,
        func: &ReceiverCall,
        method: &str,
        args: &[Arg],
        span: brass_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        let signature_params = &func.signature_params;
        let fallback_ret = func
            .declared_ret
            .clone()
            .or_else(|| self.function_returns.get(&func.symbol).cloned())
            .unwrap_or_else(|| self.fresh_unknown());
        self.check_arg_count_range(method, signature_params, args.len() + 1, span);
        // The receiver fills the first parameter.
        if let Some(first) = signature_params.first()
            && let Some(want) = param_expected_type(first)
        {
            self.expect_assignable_at(recv_ty, want, span, FlowSite::Parameter);
        }
        let mut arg_types = vec![recv_ty.clone()];
        if signature_params.len() > 1 {
            arg_types.extend(self.check_signature_args_collect(
                &signature_params[1..],
                args,
                scopes,
            ));
        } else {
            for a in args {
                arg_types.push(self.check_expr(&a.expr, scopes));
            }
        }
        self.instantiate_function_call(
            &func.symbol,
            &func.module,
            signature_params,
            &func.decl.body,
            func.declared_ret.clone(),
            fallback_ret,
            &arg_types,
            span,
        )
    }

    /// Type-check a call whose callee is a value (closure/function value)
    /// bound to the local `name`.
    fn check_callable_value(
        &mut self,
        name: &str,
        callee_ty: Type,
        args: &[Arg],
        span: brass_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        self.apply_callable(Some(name), callee_ty, args, span, scopes)
    }

    /// Type a reflective `-> infer!` method call. The result is the caller's
    /// expectation (unwrapped from a `Result`/nullable), wrapped as `key!`; the
    /// (receiver, method, key) triple is recorded so the driver generates the
    /// concrete specialization and rewrites this call to it. The template body
    /// is not elaborated here (it is generic over the key).
    fn check_keyed_method_call(
        &mut self,
        recv_ty: &Type,
        method: &str,
        args: &[Arg],
        span: brass_parser::Span,
        expected: Option<&Type>,
        scopes: &mut ScopeStack,
    ) -> Type {
        for a in args {
            self.check_expr(&a.expr, scopes);
        }
        let key = match expected.map(|t| self.resolve(t)) {
            Some(t) => match t.result_payloads() {
                Some((ok, _)) => ok.clone(),
                None => t,
            },
            None => {
                self.errors.push(TypeError {
                    message: format!(
                        "cannot infer the target type of `{method}`; annotate the \
                         destination (e.g. `let x: T = value.{method}()!`)"
                    ),
                    span,
                });
                return self.fresh_unknown();
            }
        };
        let recv_symbol = match brass_hir::peel_modes(&self.resolve(recv_ty)) {
            Type::Record(n) | Type::Sum(n) => self
                .program
                .type_by_id(n.id)
                .expect("a resolved keyed method receiver has nominal metadata")
                .symbol
                .clone(),
            other => other.type_name(),
        };
        self.record_keyed_call(span, recv_symbol, method.to_string(), key.clone());
        // The specialization's failures come from `error(..)`, whose payload
        // is the prelude `Error` wrapping the message string.
        let err = crate::lift_err_payload(self.program, Type::Str);
        Type::result(key, err)
    }

    /// Type a resolved method call (the shared tail of nominal and structural
    /// method resolution): check the signature/arity/arguments, re-elaborate
    /// each candidate body, and produce the call's result type. Body errors are
    /// re-attributed to `reattribute_to` when given (a structural receiver's
    /// value span), else to the call site for a foreign-module method.
    #[allow(clippy::too_many_arguments)]
    fn check_methods_call(
        &mut self,
        methods: Vec<ResolvedMethod>,
        recv_ty: &Type,
        method: &str,
        args: &[Arg],
        span: brass_parser::Span,
        reattribute_to: Option<brass_parser::Span>,
        scopes: &mut ScopeStack,
    ) -> Type {
        self.check_common_method_signatures(&methods, method, span);
        let first_signature = &methods[0].signature;
        let skip_self = first_signature
            .params
            .first()
            .is_some_and(|p| p.name == "self");
        // A method without a `self` parameter is static and must be
        // called as `Type.method(..)`, not through an instance.
        if !skip_self {
            self.errors.push(TypeError {
                message: format!("`{method}` is a static method; call it as `Type.{method}(...)`"),
                span,
            });
        }
        let signature_params: Vec<ParamInfo> = if skip_self {
            first_signature.params[1..].to_vec()
        } else {
            first_signature.params.clone()
        };
        self.check_arg_count_range(method, &signature_params, args.len(), span);
        // The types this receiver instance pins each parameter to (its scheme):
        // a witness-free `string -> int64` map's `set` value is `int64`. Checking
        // arguments against these lets a bare literal take the pinned width.
        let (scheme_params, pinned) = if skip_self {
            (
                self.scheme_method_param_types(recv_ty, method),
                self.scheme_method_param_pinned(recv_ty, method),
            )
        } else {
            (Vec::new(), Vec::new())
        };
        let arg_types = self.check_signature_args_collect_expected(
            &signature_params,
            args,
            &scheme_params,
            &pinned,
            scopes,
        );
        // A method defined in another module (e.g. the stdlib) is checked by
        // re-elaborating its body with this call's concrete types. When the
        // call's argument types are inconsistent with the receiver's
        // instance -- `map.get(1)` on a `string`-keyed map -- the clash
        // surfaces inside that body, at a span the caller cannot see (and the
        // LSP cannot show). Re-attribute such body errors to this call site,
        // so the inconsistency is reported where it originates.
        let foreign_method = self
            .program
            .types
            .get(&methods[0].self_type)
            .is_some_and(|t| t.module != self.current_module);
        let before = self.errors.len();
        // A body with a type test decides per instance which of its paths are
        // live -- and so what it returns, and whether it can fail at all --
        // while the scheme comes from the definitional pass, which keeps
        // every arm.
        let decided_per_instance = methods.iter().any(|resolved| {
            resolved
                .method
                .body
                .as_ref()
                .is_some_and(super::precompute::block_has_type_test)
        });
        let mut returns = Vec::with_capacity(methods.len());
        for resolved in methods {
            let declared_ret = resolved.signature.ret_ty.clone();
            let fallback_ret = declared_ret
                .clone()
                .or_else(|| {
                    self.method_returns
                        .get(&(resolved.qualifier.clone(), method.to_string()))
                        .cloned()
                })
                .unwrap_or(Type::Void);
            returns.push(self.instantiate_method_call(MethodCall {
                owner: &resolved.qualifier,
                self_type: &resolved.self_type,
                name: method,
                method: &resolved.method,
                signature_params: &resolved.signature.params,
                receiver_ty: if skip_self {
                    Some(recv_ty.clone())
                } else {
                    None
                },
                declared_ret,
                fallback_ret,
                arg_types: &arg_types,
                scheme_params: &scheme_params,
                span,
            }));
        }
        if self.errors.len() > before {
            if let Some(value_span) = reattribute_to {
                self.reattribute_errors_to_call(before, method, value_span);
            } else if foreign_method {
                self.reattribute_errors_to_call(before, method, span);
            }
        }
        // The method body ran conceptually: undo narrowings it may have
        // invalidated (see `invalidate_narrowed_after_call`).
        self.invalidate_narrowed_after_call(scopes);
        // Type the call's result by instantiating the method's scheme
        // against the receiver instance (schemes are built before the
        // function bodies that call them). The re-elaboration above still
        // ran for its conflict checks -- a key compared with `==` does not
        // unify onto a scheme parameter, so a `map.get(1)` clash is caught
        // there, not by the scheme. The re-elaborated return is the
        // fallback when the scheme cannot resolve the result.
        if decided_per_instance
            && let Some(ret) = self.common_type_list(&returns)
            && brass_hir::is_fully_known(&self.resolve(&ret))
        {
            return ret;
        }
        if let Some(ret) = self.scheme_method_return(recv_ty, method) {
            return ret;
        }
        self.common_type_list(&returns)
            .unwrap_or_else(|| self.fresh_unknown())
    }

    /// How every record type declaring `method` relates to the structural
    /// (anonymous) receiver `record`: whether the type is visible from the
    /// current module and which of its fields the value fails to provide.
    /// Sorted by name for deterministic diagnostics. Visibility is evaluated
    /// from each definition's module and the import-origin table below; doing a
    /// second bare-name lookup here would incorrectly discard renamed imports.
    fn structural_method_types(
        &mut self,
        record: &NominalType,
        method: &str,
    ) -> Vec<StructuralMethodType> {
        let infos: Vec<(String, String, Vec<String>)> = self
            .program
            .types
            .values()
            .filter_map(|info| {
                let TypeKind::Record { methods, .. } = &info.kind else {
                    return None;
                };
                if !methods.contains_key(method) {
                    return None;
                }
                Some((info.name.clone(), info.symbol.clone(), info.module.clone()))
            })
            .collect();
        let mut out: Vec<StructuralMethodType> = Vec::new();
        for (name, symbol, module) in infos {
            let Some(info) = self.program.types.get(&symbol) else {
                continue;
            };
            let sup = info.type_ref();
            let Type::Record(sup_n) = &sup else { continue };
            let unsatisfied =
                crate::structural::record_satisfies_fields(self.program, record, sup_n);
            let visible = self.is_nominal_visible(&module, &name);
            out.push(StructuralMethodType {
                name,
                symbol,
                visible,
                unsatisfied,
            });
        }
        out.sort_by(|a, b| a.name.cmp(&b.name));
        out
    }

    /// The record types that declare method `method`, are visible from the
    /// current module (declared in it or imported into it), AND whose declared
    /// fields the structural (anonymous) instance `record` satisfies. A type
    /// the module never imported must not capture an anonymous value, even
    /// when the shape matches: the author has not named it here.
    pub(super) fn structural_method_candidates(
        &mut self,
        record: &NominalType,
        method: &str,
    ) -> Vec<(String, String)> {
        self.structural_method_types(record, method)
            .into_iter()
            .filter(|t| t.visible && t.unsatisfied.is_empty())
            .map(|t| (t.name, t.symbol))
            .collect()
    }

    /// A near-miss explanation for a failed structural method resolution, in
    /// preference order: a type the value satisfies exists but is not imported
    /// into this module (the import is the fix), or in-scope types declare
    /// `method` but the value lacks some of their members. `None` when no type
    /// resolvable from here declares the method at all (the plain
    /// has-no-method error reads better then).
    fn structural_near_miss(&mut self, record: &NominalType, method: &str) -> Option<String> {
        let types = self.structural_method_types(record, method);
        let hidden: Vec<&str> = types
            .iter()
            .filter(|t| !t.visible && t.unsatisfied.is_empty())
            .map(|t| t.name.as_str())
            .collect();
        match hidden.as_slice() {
            [] => {}
            [name] => {
                return Some(format!(
                    "the anonymous structure satisfies `{name}`, which declares \
                     `{method}`, but `{name}` is not imported into this module"
                ));
            }
            names => {
                return Some(format!(
                    "the anonymous structure satisfies `{}`, which all declare \
                     `{method}`, but none of them is imported into this module",
                    names.join("`, `")
                ));
            }
        }
        let misses: Vec<String> = types
            .iter()
            .filter(|t| t.visible && !t.unsatisfied.is_empty())
            .map(|t| format!("`{}` (unsatisfied: {})", t.name, t.unsatisfied.join(", ")))
            .collect();
        if misses.is_empty() {
            return None;
        }
        Some(format!(
            "the anonymous structure does not satisfy any in-scope type declaring \
             `{method}`: {}",
            misses.join("; ")
        ))
    }

    /// The stored type of record field `name` on instance `record`, if the field
    /// exists: the instance substitution (an inferred field pinned at
    /// construction) wins over the declaration's annotation. `None` when the
    /// record has no such field.
    fn field_value_type(&mut self, record: &NominalType, name: &str) -> Option<Type> {
        if let Some(t) = record.substitution.get(name) {
            return Some(t.clone());
        }
        let info = self.program.type_by_id(record.id)?;
        let TypeKind::Record { fields, .. } = &info.kind else {
            return None;
        };
        let f = fields.iter().find(|f| f.name == name)?;
        Some(
            f.resolved_ty
                .clone()
                .unwrap_or_else(|| self.fresh_unknown()),
        )
    }

    /// Apply a callable value of type `callee_ty` to `args`: check argument
    /// compatibility for a `Fun` type and yield the call's result type. Each
    /// argument is checked exactly once here. `callee` names the value for
    /// diagnostics when it is a plain name.
    fn apply_callable(
        &mut self,
        callee: Option<&str>,
        callee_ty: Type,
        args: &[Arg],
        span: brass_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        match self.resolve_head(&callee_ty) {
            Type::Fun(params, ret) => {
                self.check_arg_count("<closure>", params.len(), args.len(), span);
                self.check_read_only_value_args(span, &params);
                // A function value is monomorphic: each argument is checked
                // against its parameter type and an open parameter is
                // committed to the argument in the solver, so this
                // application fixes the closure's type and every other
                // application must agree with it (a `let` binding's numeric
                // parameter may already be fixed at the join of its direct
                // applications, see `closure_applications`). A generalized
                // closure binding reaches here already instantiated for this
                // one use (`instantiate_closure_scheme`), so committing its
                // fresh variables pins nothing another use sees.
                for (idx, arg) in args.iter().enumerate() {
                    if let Some(param) = params.get(idx) {
                        let mut expected = self.resolve(param);
                        let open = !brass_hir::is_fully_known(&expected);
                        if matches!(arg.expr, Expr::Array(..))
                            && matches!(expected, Type::Array(..) | Type::Slice(..))
                            && !brass_hir::is_fully_known(&expected)
                        {
                            // An open array expectation alone loses the literal's
                            // element type. Fill its holes from this argument so
                            // concrete closure-body checking sees the real shape.
                            let actual = self.check_expr(&arg.expr, scopes);
                            expected = self.instantiate_annotated_type(&expected, &actual);
                        }
                        let got = self.check_expr_against(&arg.expr, &expected, scopes);
                        if self.reject_void_argument(&got, arg.expr.span()) {
                            continue;
                        }
                        // Verify any structural constraints the closure body
                        // recorded on this still-open parameter (e.g. `(x) ->
                        // x + 1` requires a numeric argument) against the
                        // argument, then commit the parameter to it.
                        self.verify_shape_constraints(param, &got, arg.expr.span());
                        if open {
                            let _ = self.solver.unify(param, &got);
                        }
                    } else {
                        self.check_expr(&arg.expr, scopes);
                    }
                }
                let observed = self.check_callable_body(&params, &ret);
                // The generic return type may not express what this
                // application returns (`(q) -> q.b` on a record): the body
                // checked at the argument types answers then.
                let result = self.resolve(&ret);
                observed.unwrap_or(result)
            }
            // Calling a value of still-unknown type constrains it to a function:
            // unify it with `(arg types...) -> fresh_ret`. This is the application
            // rule for an inference variable, so `fun apply(f, x) { return f(x) }`
            // infers `f: (unknown) -> unknown` (and `apply` as
            // `((U) -> V, U) -> V`), letting a function argument type-check and
            // monomorphize instead of leaving `f` an uncallable unknown.
            callee_var @ Type::Unknown(id) => {
                // A function named as a value whose trailing parameters are
                // optional takes the arity of this application.
                if let Some(ret) = self.apply_function_value(id, args, span, scopes) {
                    return ret;
                }
                let arg_types: Vec<Type> = args
                    .iter()
                    .map(|arg| {
                        let got = self.check_expr(&arg.expr, scopes);
                        if self.reject_void_argument(&got, arg.expr.span()) {
                            self.fresh_unknown()
                        } else {
                            got
                        }
                    })
                    .collect();
                let ret = self.fresh_unknown();
                let fun_ty = Type::Fun(arg_types, Box::new(ret.clone()));
                // A value passed to itself (`x(x)`) would need a type that
                // contains itself; the solver refuses the binding, and the
                // call is reported rather than left as an uncallable unknown
                // the back ends cannot type.
                if self.solver.occurs(id, &fun_ty) {
                    self.errors.push(TypeError {
                        message: helpers::infinite_application_message(callee),
                        span,
                    });
                } else {
                    let _ = self.solver.unify(&callee_var, &fun_ty);
                }
                ret
            }
            resolved => {
                self.errors.push(TypeError {
                    message: format!("cannot call a value of type `{}`", resolved.display()),
                    span,
                });
                for arg in args {
                    self.check_expr(&arg.expr, scopes);
                }
                self.fresh_unknown()
            }
        }
    }

    fn check_static_call(
        &mut self,
        qualifier: &str,
        method: &str,
        args: &[Arg],
        span: brass_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        // `T.from(v)`: a *fallible* structural conversion to record type `T`,
        // unless `T` declares a static `from`, which shadows it and is called
        // below like any static method (see `conversion_target`). The
        // result is `T?` for an argument of ANY type: whether `v` actually has
        // every field `T` declares is decided per monomorphized argument type
        // (the conversion yields the record when the concrete argument has the
        // fields, else null), so neither a missing field nor an argument that is
        // not a record at all is a static error -- the caller narrows the nullable
        // (an `if`/`if let`) and handles the failure path.
        //
        // Accepting a non-record argument is what lets ONE function take a value
        // of several types and decide per instance: `if let p = Path.from(x) {..}`
        // reads as "when this is a Path", and answers null when `x` is a string.
        if method == "from"
            && let Some((ty, target_fields)) = self.conversion_target(qualifier)
        {
            // Every argument is still type-checked (an undeclared name in a
            // trailing argument must surface) -- but no argument TYPE is
            // required: any value may be offered to the conversion. The arity
            // is exactly one.
            for arg in args {
                match &arg.expr {
                    Expr::TypeLit(name, fields, _) if name.is_empty() => {
                        self.check_from_source_literal(&arg.expr, fields, &target_fields, scopes);
                    }
                    other => {
                        self.check_expr(other, scopes);
                    }
                }
            }
            if args.len() != 1 {
                self.errors.push(TypeError {
                    message: format!("`{qualifier}.from` takes 1 argument, found {}", args.len()),
                    span,
                });
            }
            return Type::Nullable(Box::new(ty));
        }
        if let Some(ret) = self.primitive_static_call(qualifier, method, args, scopes) {
            return ret;
        }
        if let Some(resolved) = self.method_for_qualifier(qualifier, method) {
            let signature_params = resolved.signature.params.clone();
            self.check_arg_count_range(method, &signature_params, args.len(), span);
            let arg_types = self.check_signature_args_collect(&signature_params, args, scopes);
            let declared_ret = resolved.signature.ret_ty.clone();
            let fallback_ret = declared_ret
                .clone()
                .or_else(|| {
                    self.method_returns
                        .get(&(resolved.qualifier.clone(), method.to_string()))
                        .cloned()
                })
                .unwrap_or_else(|| self.fresh_unknown());
            return self.instantiate_method_call(MethodCall {
                owner: &resolved.qualifier,
                self_type: &resolved.self_type,
                name: method,
                method: &resolved.method,
                signature_params: &resolved.signature.params,
                receiver_ty: None,
                declared_ret,
                fallback_ret,
                arg_types: &arg_types,
                // A static call has no receiver instance to pin parameters.
                scheme_params: &[],
                span,
            });
        }
        args.iter().for_each(|a| {
            self.check_expr(&a.expr, scopes);
        });
        // Nothing resolved the call: not a record/sum method (through the
        // qualifier or a type alias of it), not a primitive static, not a
        // structural `from`. An open result would let `check` pass and the
        // back end fail with an unrelated-looking lowering error, so report it
        // here. An empty qualifier is `Self` outside any type; the resolution
        // error is reported elsewhere.
        if !qualifier.is_empty() {
            self.errors.push(TypeError {
                message: format!("`{qualifier}` has no static method `{method}`"),
                span,
            });
        }
        self.fresh_unknown()
    }

    /// Check every anonymous structural argument of a free-function call
    /// against the callee parameter's derived row (see
    /// `brass_typesys::rows`): a Required field must be present with a type
    /// satisfying its Forced type; Guarded fields tolerate absence/mismatch
    /// (they degrade to null in the view). Errors land on the argument's own
    /// span -- the value is where the mismatch lives, not the callee body.
    ///
    /// Returns `None` when a row rejected an argument (the caller skips the
    /// body re-elaboration: it would only restate the failure at interior
    /// spans). On success, each checked argument to a view-ELIGIBLE parameter
    /// is recorded in `view_args` for MIR lowering's view conversion, and the
    /// returned argument types carry its view (`brass_typesys::view_type`) in
    /// place of the argument's own type -- the type the callee body is
    /// elaborated, and compiled, at.
    fn check_args_against_rows(
        &mut self,
        name: &str,
        symbol: &str,
        args: &[Arg],
        arg_types: &[Type],
    ) -> Option<Vec<Type>> {
        let mut ok = true;
        let mut elaboration_types = arg_types.to_vec();
        for (idx, arg) in args.iter().enumerate() {
            let Some(arg_ty) = arg_types.get(idx) else {
                continue;
            };
            let Some(prow) = self.rows.function_param(symbol, idx) else {
                continue;
            };
            if !prow.eligible {
                // The parameter needs the full value (method receiver, escape,
                // annotated forward): keep the re-elaboration/reattribution path.
                continue;
            }
            let resolved = self.resolve(arg_ty);
            let Type::Record(n) = brass_hir::peel_modes(&resolved) else {
                continue;
            };
            if n.id != brass_hir::STRUCTURAL_RECORD_ID {
                continue;
            }
            let row = prow.row.clone();
            let fields: Vec<(String, Type)> = n
                .substitution
                .iter()
                .map(|(k, v)| (k.to_string(), self.resolve(v)))
                .collect();
            let issues = brass_typesys::check_row(&row, &fields);
            if issues.is_empty() {
                self.record_view_arg(arg.expr.span());
                if let Ok(view) = brass_typesys::view_type(&row, n) {
                    elaboration_types[idx] = view;
                }
            } else {
                ok = false;
                for issue in issues {
                    self.errors.push(TypeError {
                        message: format!("this value does not fit `{name}`'s parameter: {issue}"),
                        span: arg.expr.span(),
                    });
                }
            }
        }
        ok.then_some(elaboration_types)
    }

    /// Elaborate the prelude `error` body at one call's argument types, as
    /// any call elaborates its callee: the call's TYPE is special-cased (see
    /// `check_call`), but the body still runs per instance, and its
    /// constructions must be observed per instance like any generic body's.
    /// Otherwise the lazy pipeline, which checks a demanded body once at the
    /// first instance it is asked for, would publish that instance's
    /// construction types as every instance's (an `error(n)` with an `int32`
    /// payload building an `Error` of the first call's `string`).
    fn elaborate_error_body(&mut self, params: &[ParamInfo], arg_types: &[Type], span: Span) {
        let Some(info) = self.lookup_function("error") else {
            return;
        };
        let (symbol, module, body, declared) = (
            info.symbol.clone(),
            info.module.clone(),
            info.decl.body.clone(),
            info.signature.ret_ty.clone(),
        );
        let fallback = self.fresh_unknown();
        self.instantiate_function_call(
            &symbol, &module, params, &body, declared, fallback, arg_types, span,
        );
    }

    fn check_signature_args_collect(
        &mut self,
        params: &[ParamInfo],
        args: &[Arg],
        scopes: &mut ScopeStack,
    ) -> Vec<Type> {
        self.check_signature_args_collect_expected(params, args, &[], &[], scopes)
    }

    /// Check a call's arguments, preferring the receiver-instantiated parameter
    /// type from the type's scheme (`scheme_params`) over the parameter's own
    /// annotation. This lets an argument to a witness-free container method take
    /// the receiver's pinned type: a bare integer literal `set` into a
    /// `string -> int64` map is checked against `int64` (so it types as int64
    /// rather than defaulting to int32), and an int32 argument widens at the
    /// call boundary.
    ///
    /// An argument is a parameter flow (the callee is instantiated at its own
    /// type), except where `pinned` marks the receiver instance as fixing the
    /// parameter's type: the method stores that argument in the receiver's
    /// own slots (a map's key or value), so it is checked as storage.
    fn check_signature_args_collect_expected(
        &mut self,
        params: &[ParamInfo],
        args: &[Arg],
        scheme_params: &[Option<Type>],
        pinned: &[bool],
        scopes: &mut ScopeStack,
    ) -> Vec<Type> {
        let mut arg_types = Vec::with_capacity(args.len());
        let mut origins = Vec::new();
        for (idx, arg) in args.iter().enumerate() {
            let scheme_want = scheme_params.get(idx).and_then(|o| o.as_ref());
            let site = if scheme_want.is_some() && pinned.get(idx).copied().unwrap_or(false) {
                FlowSite::Storage
            } else {
                FlowSite::Parameter
            };
            let want = scheme_want.or_else(|| params.get(idx).and_then(param_expected_type));
            let got = if let Some(want) = want.cloned() {
                self.check_expr_against_at(&arg.expr, &want, site, scopes)
            } else {
                self.check_expr(&arg.expr, scopes)
            };
            // A rejected `void` argument instantiates the callee open rather
            // than at `void`, so its body does not report the same mistake
            // again from inside.
            let got = if self.reject_void_argument(&got, arg.expr.span()) {
                self.fresh_unknown()
            } else {
                got
            };
            let (got, origin) = if self.numeric.active && want.is_none() {
                self.numeric_argument(&arg.expr, &got)
            } else {
                (got, None)
            };
            if self.numeric.probing {
                origins.push(origin);
            }
            if self.numeric_enabled
                && !self.numeric.active
                && want.is_none()
                && brass_typesys::NumericLiteral::of_expr(&arg.expr).is_some()
            {
                self.record_typed(
                    brass_hir::TypedExprKind::NumericArgument,
                    arg.expr.span(),
                    got.clone(),
                    Constness::Unknown,
                );
            }
            arg_types.push(got);
        }
        if self.numeric.probing {
            self.numeric
                .arguments
                .insert(self.numeric.calls.clone(), origins);
        }
        // A call may omit a trailing `Location` parameter (MIR fills it with
        // the call site); complete the collected types so the callee still
        // instantiates at full arity.
        if arg_types.len() + 1 == params.len()
            && params
                .last()
                .is_some_and(|p| param_is_location(self.program, p))
            && let Some(loc) = self.location_instance()
        {
            arg_types.push(loc);
        }
        arg_types
    }

    /// Reject an argument whose value is `void`. A parameter binds a name,
    /// and a `void` call result has no value to bind -- exactly as `let y =
    /// f()` is rejected -- so the call it comes from is a mistake (classically
    /// a block-bodied closure or function without an explicit `return`).
    /// Returns whether the argument was rejected.
    fn reject_void_argument(&mut self, got: &Type, span: brass_parser::Span) -> bool {
        let void = matches!(self.resolve(got), Type::Void);
        if void {
            self.errors.push(TypeError {
                message: "cannot pass a `void` value as an argument: a parameter binds a \
                          name, and the call it comes from returns no value (a block-bodied \
                          closure or function returns `void` without an explicit `return`)"
                    .to_string(),
                span,
            });
        }
        void
    }

    /// The prelude `Location` record instance a filled implicit argument has.
    fn location_instance(&self) -> Option<Type> {
        self.program
            .prelude_type("Location")
            .map(brass_hir::TypeInfo::type_ref)
    }

    /// Move the body errors a foreign method produced (when re-elaborated for a
    /// call) onto the call site `span`, framed as a receiver/argument mismatch, so
    /// they are reported where the user wrote the call rather than at an
    /// unreachable span inside the stdlib. Identical re-pointed errors are
    /// deduplicated, since one inconsistency can surface at several body sites.
    fn reattribute_errors_to_call(
        &mut self,
        before: usize,
        method: &str,
        span: brass_parser::Span,
    ) {
        self.reattribute_errors(
            before,
            &format!("call to `{method}` here does not match the receiver's type"),
            span,
        );
    }

    /// Move the errors recorded past `before` onto `span`, prefixed with
    /// `frame` (deduplicated -- one inconsistency can surface at several body
    /// sites). Used to point a callee-body re-elaboration failure at the
    /// caller's value instead of a span inside the callee.
    fn reattribute_errors(&mut self, before: usize, frame: &str, span: brass_parser::Span) {
        let mut seen: HashSet<String> = HashSet::default();
        let kept: Vec<TypeError> = self
            .errors
            .split_off(before)
            .into_iter()
            .filter_map(|e| {
                let message = format!("{frame}: {}", e.message);
                seen.insert(message.clone())
                    .then_some(TypeError { message, span })
            })
            .collect();
        self.errors.extend(kept);
    }

    pub(super) fn check_arg_count(
        &mut self,
        name: &str,
        want: usize,
        got: usize,
        span: brass_parser::Span,
    ) {
        if want != got {
            self.errors.push(TypeError {
                message: format!("`{name}` expects {want} argument(s), got {got}"),
                span,
            });
        }
    }

    /// Check arity allowing a trailing run of nullable parameters to be omitted
    /// (each defaults to `null`): the supplied count must be between the required
    /// minimum and the full parameter count.
    fn check_arg_count_range(
        &mut self,
        name: &str,
        params: &[ParamInfo],
        got: usize,
        span: brass_parser::Span,
    ) {
        let min = required_arg_count(self.program, params);
        self.check_arg_count_range_counts(name, min, params.len(), got, span);
    }

    /// Report `got` arguments outside `min..=max` for the callable `name`.
    pub(super) fn check_arg_count_range_counts(
        &mut self,
        name: &str,
        min: usize,
        max: usize,
        got: usize,
        span: brass_parser::Span,
    ) {
        if got < min || got > max {
            let want = if min == max {
                format!("{max}")
            } else {
                format!("{min} to {max}")
            };
            self.errors.push(TypeError {
                message: format!("`{name}` expects {want} argument(s), got {got}"),
                span,
            });
        }
    }
}
