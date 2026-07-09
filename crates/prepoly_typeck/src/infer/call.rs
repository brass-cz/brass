//! Call typing: dispatching a call expression to free functions,
//! builtin and primitive methods, user methods (keyed, structural, or
//! by receiver), callable values, and static type-qualified calls;
//! plus argument checking against signatures, arity validation, and
//! re-attribution of argument errors to the call site.

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
    pub(super) fn check_call(
        &mut self,
        callee: &Expr,
        args: &[Arg],
        span: prepoly_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        // Consume the caller's expectation (a keyed `-> infer!` method reads it);
        // taking it here keeps an argument's own calls from reusing it.
        let call_expected = self.call_expected.take();
        if let Expr::Ident(name, _) = callee {
            if name == "fields" {
                self.errors.push(TypeError {
                    message: "`fields(..)` is a compile-time construct, usable only as a \
                              `for` loop iterable"
                        .to_string(),
                    span,
                });
                return self.fresh_unknown();
            }
            // `typeof(x)` in value position: a compile-time string constant, the
            // source name of x's static type (the same construct also names a
            // type in type/receiver position; see resolve_annotation and
            // static_qualifier). Resolved here and recorded for MIR lowering.
            if name == "typeof" {
                let [arg] = args else {
                    self.errors.push(TypeError {
                        message: format!("`typeof` takes 1 argument, found {}", args.len()),
                        span,
                    });
                    for a in args {
                        self.check_expr(&a.expr, scopes);
                    }
                    return Type::Str;
                };
                let arg_ty = self.check_expr(&arg.expr, scopes);
                self.type_names
                    .insert(span, self.resolve(&arg_ty).type_name());
                return Type::Str;
            }
            if name == "error" {
                let err_ty = args
                    .first()
                    .map(|a| self.check_expr(&a.expr, scopes))
                    .unwrap_or(Type::Void);
                return Type::result(self.fresh_unknown(), err_ty);
            }
            if let Some(ret) = self.builtin_function_type(name, args, span, scopes) {
                return ret;
            }
            // A local binding (e.g. a closure parameter) shadows a same-named
            // global function, matching codegen's resolution order.
            if let Some(local) = self.lookup(scopes, name) {
                // Record the callee's type so hover can recover it. Applying it
                // below constrains an unknown callee to a function type, and the
                // final zonking pass then resolves this recorded type through it,
                // so `fun apply(f, x) { f(x) }` shows `f` as `(U) -> V`.
                self.record_expr_type(callee, &local);
                let ret = self.check_callable_value(local, args, span, scopes);
                self.invalidate_narrowed_after_call(scopes);
                return ret;
            }
            // Only a function visible from the current module resolves here; a
            // function defined in another, non-imported module is invisible and
            // falls through to the unknown-name path below. The
            // lookup is module-aware so a name defined in several modules
            // resolves to this module's own or imported definition (R2).
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
                // Record a fully-concrete call instance for static
                // monomorphization.
                let resolved_args: Vec<Type> = arg_types.iter().map(|t| self.resolve(t)).collect();
                if resolved_args.iter().all(is_concrete_type) {
                    let entry = self.fn_instances.entry(symbol.clone()).or_default();
                    if !entry.iter().any(|t| t == &resolved_args) {
                        tracing::debug!(
                            symbol = %symbol,
                            args = ?resolved_args.iter().map(|t| t.display()).collect::<Vec<_>>(),
                            "recording new monomorphization instance"
                        );
                        entry.push(resolved_args);
                    }
                }
                // An ANONYMOUS structural argument to a row-covered eligible
                // parameter is checked against the callee's derived row HERE, at
                // the value's own span: presence of every Required field and its
                // Forced type. This replaces the body re-elaboration as the error
                // source for these arguments -- on a row failure the body is not
                // re-elaborated at all (the call is already known bad; interior
                // spans would only duplicate the value-site report). A clean row
                // check records the argument span so lowering may convert the
                // argument into the parameter's view.
                if !self.check_args_against_rows(name, &symbol, args, &arg_types) {
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
                    &arg_types,
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
                                prepoly_hir::peel_modes(&self.resolve(t)),
                                Type::Record(n) if n.id == prepoly_hir::STRUCTURAL_RECORD_ID
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
            // `println` when the stdlib is not loaded) still defers below; any
            // other name is undeclared and reported here rather than collapsing
            // to a fresh unknown.
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
        if let Expr::Field(base, method, _) = callee {
            if let Some(qualifier) = self.static_qualifier(base, scopes) {
                // A `typeof(v)` qualifier resolves to v's type NAME; record it at
                // the inner `typeof(v)` span so MIR routes the static call (the
                // same channel that folds a value-position `typeof` to its name).
                if let Expr::Call(c, cargs, tspan) = &**base
                    && matches!(&**c, Expr::Ident(n, _) if n == "typeof")
                {
                    for a in cargs {
                        self.check_expr(&a.expr, scopes);
                    }
                    self.type_names.insert(*tspan, qualifier.clone());
                }
                let ret = self.check_static_call(&qualifier, method, args, span, scopes);
                self.invalidate_narrowed_after_call(scopes);
                return ret;
            }
            let recv_ty = self.check_expr(base, scopes);
            if let Type::Nullable(_) = self.resolve(&recv_ty) {
                self.report_nullable_use(base.span());
            }
            if let Some(ret) = self.builtin_method_type(&recv_ty, method, args, scopes, span) {
                return ret;
            }
            // A reflective `-> infer!` method is keyed by the caller's
            // expectation: its result type is fixed per call site, and the
            // driver generates a concrete specialization per key (this call is
            // rewritten to it). The template body is not elaborated here.
            if let Some(methods) = self.methods_for_type(&recv_ty, method)
                && methods
                    .first()
                    .is_some_and(|m| prepoly_hir::keyed_return(m.method.ret.as_ref()))
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
            if let Some(methods) = self.methods_for_type(&recv_ty, method) {
                return self
                    .check_methods_call(methods, &recv_ty, method, args, span, None, scopes);
            }
            // A stdlib method on a primitive/array receiver (`fun string.split`,
            // `fun infer[].map`): dispatched by the receiver's class. There is no
            // UFCS fallback -- a free function is not callable through `recv.f()`.
            if let Some(ret) =
                self.check_primitive_method_call(&recv_ty, method, args, span, scopes)
            {
                // Stdlib primitive methods are user-defined prepoly code.
                self.invalidate_narrowed_after_call(scopes);
                return ret;
            }
            // The missing-method diagnostics below look through mode wrappers so
            // a `ref(mut(T))` receiver reports against `T` instead of deferring.
            let peeled_recv = prepoly_hir::peel_modes(&self.resolve(&recv_ty)).clone();
            if let Type::Record(record) = &peeled_recv {
                // A function-typed FIELD is callable through the same syntax (a
                // method of the same name takes precedence, resolved above):
                // `a.func(4)` calls the closure the field holds.
                if let Some(fty) = self.field_value_type(record, method) {
                    let resolved = self.resolve(&fty);
                    if matches!(resolved, Type::Fun(..) | Type::Unknown(_)) {
                        self.record_expr_type(callee, &fty);
                        let ret = self.apply_callable(fty, args, span, scopes);
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
                if record.id == prepoly_hir::STRUCTURAL_RECORD_ID {
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
            // A primitive receiver has a fully known type with no user methods,
            // so an unresolved call is a static error rather than deferred
            // structural dispatch (shape constraints).
            let resolved = peeled_recv;
            if is_concrete_primitive(&resolved) {
                self.errors.push(TypeError {
                    message: format!("`{}` has no method `{method}`", resolved.display()),
                    span,
                });
                for a in args {
                    self.check_expr(&a.expr, scopes);
                }
                return self.fresh_unknown();
            }
            // Otherwise the member resolves at runtime (builtin methods, or
            // deferred structural dispatch). If the receiver is an unknown
            // inference variable, record that it must expose this method so a
            // closure like `(x) -> x.speak()` rejects an `int32` argument at
            // its call site. Evaluate the args and defer.
            if let Type::Unknown(_) = resolved {
                self.record_shape(&recv_ty, ShapeConstraint::HasMethod(method.to_string()));
            }
            for a in args {
                self.check_expr(&a.expr, scopes);
            }
            return self.fresh_unknown();
        }
        let callee_ty = self.check_expr(callee, scopes);
        let ret = self.apply_callable(callee_ty, args, span, scopes);
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
        span: prepoly_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        // Mode wrappers are peeled so a `ref(string)` / `mut(T[])` receiver still
        // dispatches to the stdlib primitive method of the underlying class.
        let class = prepoly_hir::peel_modes(&self.resolve(recv_ty)).primitive_class()?;
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
        span: prepoly_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        let signature_params = &func.signature_params;
        let fallback_ret = func
            .declared_ret
            .clone()
            .or_else(|| self.function_returns.get(&func.symbol).cloned())
            .unwrap_or_else(|| self.fresh_unknown());
        self.check_arg_count(method, signature_params.len(), args.len() + 1, span);
        // The receiver fills the first parameter.
        if let Some(first) = signature_params.first()
            && let Some(want) = param_expected_type(first)
        {
            self.expect_assignable(recv_ty, want, span);
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
        )
    }

    /// Type-check a call whose callee is a value (closure/function value).
    fn check_callable_value(
        &mut self,
        callee_ty: Type,
        args: &[Arg],
        span: prepoly_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        self.apply_callable(callee_ty, args, span, scopes)
    }

    /// Given a resolved callee type, check argument compatibility for `Fun`
    /// types and yield the call's result type. Each argument is checked exactly
    /// once here.
    /// Type a resolved method call (the shared tail of nominal and structural
    /// method resolution): check the signature/arity/arguments, re-elaborate
    /// each candidate body, and produce the call's result type. Body errors are
    /// re-attributed to `reattribute_to` when given (a structural receiver's
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
        span: prepoly_parser::Span,
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
        let recv_name = match prepoly_hir::peel_modes(&self.resolve(recv_ty)) {
            Type::Record(n) | Type::Sum(n) => n.name.clone(),
            other => other.type_name(),
        };
        self.keyed_calls
            .insert(span, (recv_name, method.to_string(), key.clone()));
        Type::result(key, Type::Str)
    }

    /// value span), else to the call site for a foreign-module method.
    #[allow(clippy::too_many_arguments)]
    fn check_methods_call(
        &mut self,
        methods: Vec<ResolvedMethod>,
        recv_ty: &Type,
        method: &str,
        args: &[Arg],
        span: prepoly_parser::Span,
        reattribute_to: Option<prepoly_parser::Span>,
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
        self.check_arg_count(method, signature_params.len(), args.len(), span);
        // The types this receiver instance pins each parameter to (its scheme):
        // a witness-free `string -> int64` map's `set` value is `int64`. Checking
        // arguments against these lets a bare literal take the pinned width.
        let scheme_params = if skip_self {
            self.scheme_method_param_types(recv_ty, method)
        } else {
            Vec::new()
        };
        let arg_types = self.check_signature_args_collect_expected(
            &signature_params,
            args,
            &scheme_params,
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
        if let Some(ret) = self.scheme_method_return(recv_ty, method) {
            return ret;
        }
        self.common_type_list(&returns)
            .unwrap_or_else(|| self.fresh_unknown())
    }

    /// How every record type declaring `method` relates to the structural
    /// (anonymous) receiver `record`: whether the type is visible from the
    /// current module and which of its fields the value fails to provide.
    /// Sorted by name for deterministic diagnostics. Only types whose bare
    /// name resolves from the current module to that definition are listed,
    /// so a name defined in several modules keeps its usual resolution.
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
            if self.resolve_type_symbol(&name).as_deref() != Some(symbol.as_str()) {
                continue;
            }
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
    fn structural_method_candidates(
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

    fn apply_callable(
        &mut self,
        callee_ty: Type,
        args: &[Arg],
        span: prepoly_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        match self.resolve(&callee_ty) {
            Type::Fun(params, ret) => {
                self.check_arg_count("<closure>", params.len(), args.len(), span);
                // Instantiate the (possibly polymorphic) callable for this call
                // site: unify each concrete argument into the parameter type,
                // then resolve the declared return type through that local
                // substitution. This recovers the result of an unannotated
                // closure such as `(x) -> x` applied to `int32` as `int32`
                // instead of an unconstrained unknown, so a later
                // `let s: string = f(1)` is correctly rejected.
                let mut subst = Subst::new();
                for (idx, arg) in args.iter().enumerate() {
                    if let Some(param) = params.get(idx) {
                        let got = self.check_expr_against(&arg.expr, param, scopes);
                        let _ = subst.unify(param, &got);
                        // Calling through a CONCRETE parameter type pins an open
                        // argument variable persistently: `(x) -> g(x)` with
                        // `g: (int32) -> int32` fixes `x = int32`, so the
                        // enclosing closure's recorded type is concrete (a
                        // closure stored into an unannotated record field takes
                        // its instance type from this). A parameter still
                        // carrying its own inference variables stays local-only:
                        // pinning through it would defeat let-polymorphism.
                        if self.solver.free_vars(param).is_empty()
                            && matches!(self.resolve(&got), Type::Unknown(_))
                        {
                            let _ = self.solver.unify(&got, param);
                        }
                        // Verify any structural constraints the closure body
                        // recorded on this parameter (e.g. `(x) -> x + 1`
                        // requires a numeric argument) now that the concrete
                        // argument type is known.
                        self.verify_shape_constraints(param, &got, arg.expr.span());
                    } else {
                        self.check_expr(&arg.expr, scopes);
                    }
                }
                subst.resolve_deep(&ret)
            }
            // Calling a value of still-unknown type constrains it to a function:
            // unify it with `(arg types...) -> fresh_ret`. This is the application
            // rule for an inference variable, so `fun apply(f, x) { return f(x) }`
            // infers `f: (unknown) -> unknown` (and `apply` as
            // `((U) -> V, U) -> V`), letting a function argument type-check and
            // monomorphize instead of leaving `f` an uncallable unknown.
            callee @ Type::Unknown(_) => {
                let arg_types: Vec<Type> = args
                    .iter()
                    .map(|arg| self.check_expr(&arg.expr, scopes))
                    .collect();
                let ret = self.fresh_unknown();
                let fun_ty = Type::Fun(arg_types, Box::new(ret.clone()));
                let _ = self.solver.unify(&callee, &fun_ty);
                ret
            }
            _ => {
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
        span: prepoly_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        // `T.from(v)`: a *fallible* structural conversion to record type `T`. The
        // result is `T?`: whether `v` actually has every field `T` declares is
        // decided per monomorphized argument type (the conversion yields the record
        // when the concrete argument has the fields, else null), so a missing field
        // is not a static error -- the caller narrows the nullable (an `if`/`if let`)
        // and handles the failure path.
        if method == "from" {
            let target = self
                .program
                .resolve_type(&self.current_module, qualifier)
                .and_then(|info| match &info.kind {
                    TypeKind::Record { .. } => Some(info.type_ref()),
                    _ => None,
                });
            if let Some(ty) = target {
                // Every argument is still type-checked (an undeclared name in a
                // trailing argument must surface), and the conversion's arity is
                // exactly one.
                for arg in args {
                    self.check_expr(&arg.expr, scopes);
                }
                if args.len() != 1 {
                    self.errors.push(TypeError {
                        message: format!(
                            "`{qualifier}.from` takes 1 argument, found {}",
                            args.len()
                        ),
                        span,
                    });
                }
                return Type::Nullable(Box::new(ty));
            }
        }
        if let Some(ret) = self.primitive_static_call(qualifier, method, args, scopes) {
            return ret;
        }
        if let Some(resolved) = self.method_for_qualifier(qualifier, method) {
            let signature_params = resolved.signature.params.clone();
            self.check_arg_count(method, signature_params.len(), args.len(), span);
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
            });
        }
        args.iter().for_each(|a| {
            self.check_expr(&a.expr, scopes);
        });
        self.fresh_unknown()
    }

    fn primitive_static_call(
        &mut self,
        tname: &str,
        method: &str,
        args: &[Arg],
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        let ret = self.primitive_static_type(tname, method)?;
        let arg_types: Vec<Type> = args
            .iter()
            .map(|a| self.check_expr(&a.expr, scopes))
            .collect();
        self.check_numeric_conversion_args(tname, method, &arg_types, args);
        Some(ret)
    }

    /// Constrain the source type of the numeric conversions:
    /// `intN.from`/`floatN.from` take a numeric value and `intN.parse`/
    /// `floatN.parse` take a string. Without this, `float64.from("abc")` would
    /// type-check and silently produce `0.0` at runtime. `string.from` accepts
    /// any value, so it is intentionally not constrained. Unknown arguments are
    /// deferred to the runtime.
    fn check_numeric_conversion_args(
        &mut self,
        tname: &str,
        method: &str,
        arg_types: &[Type],
        args: &[Arg],
    ) {
        let numeric_target =
            IntKind::from_name(tname).is_some() || matches!(tname, "float32" | "float64");
        if !numeric_target {
            return;
        }
        let (Some(arg_ty), Some(arg)) = (arg_types.first(), args.first()) else {
            return;
        };
        let resolved = self.resolve(arg_ty);
        if resolved.is_unknown() {
            return;
        }
        match method {
            "parse" if !matches!(resolved, Type::Str) => {
                self.errors.push(TypeError {
                    message: format!(
                        "`{tname}.parse` expects a string, found `{}`",
                        resolved.display()
                    ),
                    span: arg.expr.span(),
                });
            }
            "from" if !matches!(resolved, Type::Int(_) | Type::Float(_)) => {
                self.errors.push(TypeError {
                    message: format!(
                        "`{tname}.from` expects a numeric value, found `{}`",
                        resolved.display()
                    ),
                    span: arg.expr.span(),
                });
            }
            _ => {}
        }
    }

    /// Check every anonymous structural argument of a free-function call
    /// against the callee parameter's derived row (see
    /// `prepoly_typesys::rows`): a Required field must be present with a type
    /// satisfying its Forced type; Guarded fields tolerate absence/mismatch
    /// (they degrade to null in the view). Errors land on the argument's own
    /// span -- the value is where the mismatch lives, not the callee body.
    ///
    /// Returns `false` when a row rejected an argument (the caller skips the
    /// body re-elaboration: it would only restate the failure at interior
    /// spans). On success, each checked argument to a view-ELIGIBLE parameter
    /// is recorded in `view_args` for MIR lowering's view conversion.
    fn check_args_against_rows(
        &mut self,
        name: &str,
        symbol: &str,
        args: &[Arg],
        arg_types: &[Type],
    ) -> bool {
        let mut ok = true;
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
            let Type::Record(n) = prepoly_hir::peel_modes(&resolved) else {
                continue;
            };
            if n.id != prepoly_hir::STRUCTURAL_RECORD_ID {
                continue;
            }
            let row = prow.row.clone();
            let fields: Vec<(String, Type)> = n
                .substitution
                .iter()
                .map(|(k, v)| (k.to_string(), self.resolve(v)))
                .collect();
            let issues = prepoly_typesys::check_row(&row, &fields);
            if issues.is_empty() {
                self.view_args.insert(arg.expr.span());
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
        ok
    }

    fn check_signature_args_collect(
        &mut self,
        params: &[ParamInfo],
        args: &[Arg],
        scopes: &mut ScopeStack,
    ) -> Vec<Type> {
        self.check_signature_args_collect_expected(params, args, &[], scopes)
    }

    /// Check a call's arguments, preferring the receiver-instantiated parameter
    /// type from the type's scheme (`scheme_params`) over the parameter's own
    /// annotation. This lets an argument to a witness-free container method take
    /// the receiver's pinned type: a bare integer literal `set` into a
    /// `string -> int64` map is checked against `int64` (so it types as int64
    /// rather than defaulting to int32), and an int32 argument widens at the
    /// call boundary.
    fn check_signature_args_collect_expected(
        &mut self,
        params: &[ParamInfo],
        args: &[Arg],
        scheme_params: &[Option<Type>],
        scopes: &mut ScopeStack,
    ) -> Vec<Type> {
        let mut arg_types = Vec::with_capacity(args.len());
        for (idx, arg) in args.iter().enumerate() {
            let want = scheme_params
                .get(idx)
                .and_then(|o| o.as_ref())
                .or_else(|| params.get(idx).and_then(param_expected_type));
            let got = if let Some(want) = want.cloned() {
                self.check_expr_against(&arg.expr, &want, scopes)
            } else {
                self.check_expr(&arg.expr, scopes)
            };
            arg_types.push(got);
        }
        arg_types
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
        span: prepoly_parser::Span,
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
    fn reattribute_errors(&mut self, before: usize, frame: &str, span: prepoly_parser::Span) {
        let mut seen: HashSet<String> = HashSet::new();
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
        span: prepoly_parser::Span,
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
        span: prepoly_parser::Span,
    ) {
        let min = required_arg_count(params);
        let max = params.len();
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
