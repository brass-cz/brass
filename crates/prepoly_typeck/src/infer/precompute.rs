//! Pre-pass computation over the program's signatures before bodies
//! are checked: duplicate-parameter validation, inference of
//! unannotated function and method returns (with reconciliation of
//! multiple return/error payloads), record type schemes, and the
//! parameter scopes and global bindings the body checks start from.

use super::*;

impl<'a> Checker<'a> {
    pub(super) fn validate_param_declarations(&mut self) {
        let functions = self.program.functions.values().map(|f| {
            (
                format!("function `{}`", f.signature.name),
                f.signature.params.clone(),
            )
        });
        let methods = self
            .program
            .types
            .values()
            .flat_map(|info| match &info.kind {
                TypeKind::Record { methods, .. } => methods
                    .values()
                    .map(|m| {
                        (
                            format!("method `{}.{}`", info.name, m.signature.name),
                            m.signature.params.clone(),
                        )
                    })
                    .collect::<Vec<_>>(),
                TypeKind::Sum { variants } => variants
                    .iter()
                    .flat_map(|variant| {
                        variant.methods.values().map(|m| {
                            (
                                format!(
                                    "method `{}.{}.{}`",
                                    info.name, variant.name, m.signature.name
                                ),
                                m.signature.params.clone(),
                            )
                        })
                    })
                    .collect(),
            });
        let params_to_check: Vec<_> = functions.chain(methods).collect();
        for (owner, params) in params_to_check {
            self.report_duplicate_signature_params(&owner, &params);
        }
    }

    fn report_duplicate_signature_params(&mut self, owner: &str, params: &[ParamInfo]) {
        self.report_duplicate_param_names(
            owner,
            params.iter().map(|param| (param.name.as_str(), param.span)),
        );
    }

    pub(super) fn report_duplicate_params(&mut self, owner: &str, params: &[Param]) {
        self.report_duplicate_param_names(
            owner,
            params.iter().map(|param| (param.name.as_str(), param.span)),
        );
    }

    fn report_duplicate_param_names<'p>(
        &mut self,
        owner: &str,
        params: impl IntoIterator<Item = (&'p str, prepoly_parser::Span)>,
    ) {
        let mut seen = HashSet::new();
        for (name, span) in params {
            if !seen.insert(name) {
                self.errors.push(TypeError {
                    message: format!("duplicate parameter `{name}` in {owner}"),
                    span,
                });
            }
        }
    }

    pub(super) fn precompute_function_returns(&mut self) {
        let mut names: Vec<String> = self.program.functions.keys().cloned().collect();
        names.sort();
        for name in names {
            if self.function_returns.contains_key(&name) {
                continue;
            }
            let Some(info) = self.program.functions.get(&name) else {
                continue;
            };
            let ty = info.signature.ret_ty.clone().unwrap_or_else(|| {
                self.infer_function_return(&info.signature.params, &info.decl.body)
            });
            self.function_returns.insert(name, ty);
        }
    }

    pub(super) fn precompute_method_returns(&mut self) {
        let mut entries: Vec<(String, String, String)> = self
            .program
            .types
            .values()
            .flat_map(|info| match &info.kind {
                TypeKind::Record { methods, .. } => methods
                    .keys()
                    .map(|m| (info.name.clone(), info.name.clone(), m.clone()))
                    .collect::<Vec<_>>(),
                TypeKind::Sum { variants } => variants
                    .iter()
                    .flat_map(|variant| {
                        variant.methods.keys().map(|m| {
                            (
                                format!("{}.{}", info.name, variant.name),
                                info.name.clone(),
                                m.clone(),
                            )
                        })
                    })
                    .collect(),
            })
            .collect();
        entries.sort();
        for (qualifier, self_type, method) in entries {
            let ty = self.infer_method_return(&qualifier, &self_type, &method);
            self.method_returns.insert((qualifier, method), ty);
        }
    }

    fn infer_method_return(&mut self, qualifier: &str, self_type: &str, method: &str) -> Type {
        let Some(resolved) = self.method_for_qualifier(qualifier, method) else {
            return self.fresh_unknown();
        };
        if let Some(ty) = resolved.signature.ret_ty.clone() {
            return ty;
        }
        let signature_params = resolved.signature.params.clone();
        let decl = resolved.method;
        let Some(body) = &decl.body else {
            return Type::Void;
        };
        let saved = self.self_type.replace(self_type.to_string());
        let saved_variant = self.self_variant.clone();
        self.self_variant = qualifier
            .split_once('.')
            .map(|(_, variant)| (self_type.to_string(), variant.to_string()));
        let mut env = self.signature_param_env(&signature_params);
        // An instance method's `self` is the enclosing nominal type. Variant
        // methods use the sum type because HIR has no separate variant type.
        if signature_params.first().is_some_and(|p| p.name == "self") {
            env.insert("self".to_string(), self.type_by_name(self_type));
        }
        let mut normal = Vec::new();
        let mut props = LightProps::default();
        self.infer_returns_block(body, &mut env, &mut normal, &mut props);
        self.self_type = saved;
        self.self_variant = saved_variant;
        let normal_ty = self.reconcile_return_types(&normal, true);
        let err_ty = self.reconcile_error_payloads(&props.errors, true);
        let base = self.result_from_payloads(normal_ty, err_ty);
        wrap_null_propagated_return(base, &props.nulls)
    }

    /// Generalize every record type into a [`TypeScheme`]. Run after the per-type
    /// method bodies have been checked in one shared environment: that pass binds
    /// `self` to the bare type, so a type's methods share one field variable, and
    /// the bodies' stores/reads link a field's element to the methods' parameter
    /// and return variables (`HashMap`'s entry key/value is the `key`/`value` of
    /// `set`/`_insert` through `self.entries[i] = _Entry { .. }`). This reads the
    /// solver's solution for each field and method signature and quantifies the
    /// inference variables still free across them -- the inferred type parameters.
    pub(super) fn build_schemes(&self) -> HashMap<String, TypeScheme> {
        let mut out = HashMap::new();
        for info in self.program.types.values() {
            if let TypeKind::Record { .. } = &info.kind {
                out.insert(info.name.clone(), self.build_record_scheme(info));
            }
        }
        out
    }

    fn build_record_scheme(&self, info: &TypeInfo) -> TypeScheme {
        let TypeKind::Record { fields, methods } = &info.kind else {
            return TypeScheme::default();
        };
        let mut params: HashSet<u32> = HashSet::new();
        let resolved = |this: &Self, t: Option<&Type>| t.map(|t| this.resolve(t));
        let mut field_types = Vec::with_capacity(fields.len());
        for field in fields {
            let ty = resolved(self, field.resolved_ty.as_ref()).unwrap_or(Type::Void);
            params.extend(self.solver.free_vars(&ty));
            field_types.push((field.name.clone(), ty));
        }
        let self_ty = info.type_ref();
        let mut scheme_methods = std::collections::BTreeMap::new();
        for (name, method) in methods {
            let mut ps = Vec::with_capacity(method.signature.params.len());
            for p in &method.signature.params {
                let ty = if p.name == "self" {
                    self_ty.clone()
                } else {
                    resolved(self, p.resolved_ty.as_ref()).unwrap_or(Type::Void)
                };
                params.extend(self.solver.free_vars(&ty));
                ps.push((p.name.clone(), ty));
            }
            let ret = self
                .method_returns
                .get(&(info.name.clone(), name.clone()))
                .map(|t| self.resolve(t))
                .or_else(|| resolved(self, method.signature.ret_ty.as_ref()))
                .unwrap_or(Type::Void);
            params.extend(self.solver.free_vars(&ret));
            scheme_methods.insert(name.clone(), SchemeMethod { params: ps, ret });
        }
        let mut params: Vec<u32> = params.into_iter().collect();
        params.sort_unstable();
        TypeScheme {
            params,
            fields: field_types,
            methods: scheme_methods,
        }
    }

    fn infer_function_return(&mut self, params: &[ParamInfo], body: &Block) -> Type {
        let mut env = self.signature_param_env(params);
        let mut normal = Vec::new();
        let mut props = LightProps::default();
        self.infer_returns_block(body, &mut env, &mut normal, &mut props);
        let normal_ty = self.reconcile_return_types(&normal, true);
        let err_ty = self.reconcile_error_payloads(&props.errors, true);
        let base = self.result_from_payloads(normal_ty, err_ty);
        wrap_null_propagated_return(base, &props.nulls)
    }

    /// Combine the inferred normal (Ok) and error (Err) return payloads into a
    /// single return type. A function that only ever returns via `error(..)` /
    /// propagation still has an inferred `Ok` payload as a fresh unknown.
    ///
    /// A normal payload that is itself a `Result` is forwarded whole, never
    /// nested: the back ends Ok-wrap only bare return values (an
    /// already-fallible value passes through), so a nested
    /// `Result<Result<T>>` here would describe a value the program never
    /// builds -- the mismatch surfaces as a double-`!` unwrap that
    /// reinterprets the payload record as a Result (type confusion). This
    /// mirrors the annotated-return path, which flows `Result`-typed values
    /// whole (see `check_return`).
    pub(super) fn result_from_payloads(
        &mut self,
        normal_ty: Option<Type>,
        err_ty: Option<Type>,
    ) -> Type {
        match (normal_ty, err_ty) {
            (Some(ok), Some(err)) => {
                let resolved = self.resolve(&ok);
                if let Some((fwd_ok, fwd_err)) = resolved.result_payloads() {
                    // The forwarded Result's error payload and the body's own
                    // error sites must describe one type; prefer the concrete
                    // side when only one is known. (Two concrete but
                    // different payloads keep the forwarded one -- the same
                    // first-wins policy `reconcile_error_payloads` applies.)
                    let merged = if fwd_err.is_unknown() {
                        err
                    } else {
                        fwd_err.clone()
                    };
                    Type::result(fwd_ok.clone(), merged)
                } else {
                    Type::result(ok, err)
                }
            }
            (Some(ty), None) => ty,
            (None, Some(err)) => Type::result(self.fresh_error_only_ok(), err),
            (None, None) => Type::Void,
        }
    }

    /// Reduce the explicit `return` types of a body to a single type. Unlike
    /// `common_type_list`, this carries the span of each return so that two
    /// incompatible concrete returns (e.g. `return 1` and `return "x"`) produce
    /// a diagnostic instead of silently collapsing to a fresh `Unknown`, which
    /// would let the function's return type satisfy any annotation. `report`
    /// is false at call-site re-inference to avoid duplicating the definition
    /// site's diagnostic.
    pub(super) fn reconcile_return_types(
        &mut self,
        normal: &[(Type, Span)],
        report: bool,
    ) -> Option<Type> {
        let (first, rest) = normal.split_first()?;
        let mut common = first.0.clone();
        for (ty, span) in rest {
            if let Some(nullable) = common_nullable_type(&common, ty) {
                common = nullable;
                continue;
            }
            if !self.can_unify(&common, ty) {
                if report {
                    self.errors.push(TypeError {
                        message: format!(
                            "incompatible return types: `{}` and `{}`",
                            self.resolve(&common).display(),
                            self.resolve(ty).display()
                        ),
                        span: *span,
                    });
                }
                // Keep the first concrete type so callers check against a
                // definite type rather than cascading a second error.
                return Some(common);
            }
        }
        Some(common)
    }

    /// Reduce the inferred `Err` payloads of a fallible body to a single type.
    /// A function whose error payload comes from both a propagated `expr!` and
    /// a local `error(x)` must agree on one payload type; two
    /// incompatible concrete payloads are a diagnostic rather than a silent
    /// collapse to a fresh `Unknown` that would accept any later use. `report`
    /// is false at call-site re-inference so the definition site is not
    /// duplicated.
    pub(super) fn reconcile_error_payloads(
        &mut self,
        errors: &[(Type, Span)],
        report: bool,
    ) -> Option<Type> {
        let (first, rest) = errors.split_first()?;
        let mut common = first.0.clone();
        for (ty, span) in rest {
            if let Some(nullable) = common_nullable_type(&common, ty) {
                common = nullable;
                continue;
            }
            if !self.can_unify(&common, ty) {
                if report {
                    self.errors.push(TypeError {
                        message: format!(
                            "incompatible error payloads: `{}` and `{}`",
                            self.resolve(&common).display(),
                            self.resolve(ty).display()
                        ),
                        span: *span,
                    });
                }
                return Some(common);
            }
        }
        Some(common)
    }

    pub(super) fn param_scope(&mut self, params: &[Param]) -> HashMap<String, Type> {
        params
            .iter()
            .map(|p| {
                let ty =
                    p.ty.as_ref()
                        .and_then(|t| self.resolve_type(t).ok())
                        .unwrap_or_else(|| self.fresh_unknown());
                (p.name.clone(), ty)
            })
            .collect()
    }

    fn signature_param_scope(&mut self, params: &[ParamInfo]) -> HashMap<String, Type> {
        params
            .iter()
            .map(|param| {
                let ty = param
                    .resolved_ty
                    .clone()
                    .unwrap_or_else(|| self.fresh_unknown());
                (param.name.clone(), ty)
            })
            .collect()
    }

    /// Infer the types of top-level `let`/`const` bindings in module/source
    /// order and record them in `global_scope`. Bindings
    /// accumulate as iteration proceeds, so a later global is never visible to
    /// an earlier initializer. Annotation resolution errors are surfaced by
    /// `resolve_annotations`, so they are intentionally swallowed here.
    pub(super) fn precompute_global_bindings(&mut self) {
        let program = self.program;
        let mut env: HashMap<String, Type> = HashMap::new();
        let mut props = LightProps::default();
        for init in &program.inits {
            for stmt in &init.stmts {
                let Stmt::Let { pat, ty, value, .. } = stmt else {
                    continue;
                };
                let Some(value) = value else {
                    // A module-level binding is a global initialized by the
                    // module's init; without an initializer there is no init
                    // order at which it becomes defined.
                    self.errors.push(TypeError {
                        message: "a top-level `let` needs an initializer".to_string(),
                        span: stmt.span(),
                    });
                    continue;
                };
                let value_ty = self.infer_expr_light(value, &env, &mut props);
                let binding_ty = match ty {
                    Some(te) => match self.resolve_type(te) {
                        Ok(annotated) => self.instantiate_annotated_type(&annotated, &value_ty),
                        Err(_) => value_ty,
                    },
                    None => value_ty,
                };
                self.bind_pattern_light(pat, &binding_ty, &mut env);
            }
        }
        self.global_scope = env;
    }

    /// The scope stack used to check a function or method body: top-level
    /// globals at the bottom, signature parameters on top so parameters shadow
    /// same-named globals.
    pub(super) fn signature_scopes(&mut self, params: &[ParamInfo]) -> ScopeStack {
        vec![
            self.global_scope.clone(),
            self.signature_param_scope(params),
        ]
    }

    /// A single-scope environment for return inference that layers signature
    /// parameters over the globals, mirroring `signature_scopes` shadowing.
    fn signature_param_env(&mut self, params: &[ParamInfo]) -> HashMap<String, Type> {
        let mut env = self.global_scope.clone();
        env.extend(self.signature_param_scope(params));
        env
    }
}

/// Wrap a body's inferred return in an outer `?` when it contains a
/// nullable-operand `expr!` (`nulls` non-empty): the null case returns null
/// from the callable. A void base stays void (a statement use has no value a
/// caller could observe) and an already-nullable base is not double-wrapped.
pub(super) fn wrap_null_propagated_return(base: Type, nulls: &[Span]) -> Type {
    if nulls.is_empty() {
        return base;
    }
    match base {
        Type::Void | Type::Nullable(_) => base,
        other => Type::Nullable(Box::new(other)),
    }
}
