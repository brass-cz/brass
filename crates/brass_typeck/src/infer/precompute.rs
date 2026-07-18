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
        params: impl IntoIterator<Item = (&'p str, brass_parser::Span)>,
    ) {
        let mut seen = HashSet::default();
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
            let ty = self.function_return_entry(info);
            self.function_returns.insert(name, ty);
        }
    }

    /// Re-infer every UNANNOTATED function return, replacing the first pass's
    /// answer.
    ///
    /// The first pass necessarily runs before any method return exists (a
    /// method's body calls free functions, so its own pass needs theirs), which
    /// leaves a function whose value flows OUT of a method call with nothing to
    /// read: `http`'s `fetch` returns `client.fetch(path)`, and with
    /// `HttpClient.fetch` still unknown the light pass could only give the
    /// return a bare variable -- reported as `Result<unknown, string>` once the
    /// body's own `error(..)` propagation supplied the Err payload. Running the
    /// two in alternation closes that loop, exactly as repeating
    /// `precompute_method_returns` closes it for cross-TYPE method chains.
    ///
    /// A FULLY-KNOWN annotation is skipped: its entry is the declaration itself
    /// and re-inferring it would be both wasted work and a chance to disagree with
    /// what the checker enforces. A `T!` annotation is not fully known -- it names
    /// only the OK payload -- so its Err side is completed here.
    pub(super) fn refresh_function_returns(&mut self) {
        let mut names: Vec<String> = self.program.functions.keys().cloned().collect();
        names.sort();
        for name in names {
            let Some(info) = self.program.functions.get(&name) else {
                continue;
            };
            // A seeded context function's return is already in the table.
            if self.seeded_module(&info.module) {
                continue;
            }
            // A fully-known annotation is the declaration itself: re-inferring it
            // would be wasted work and a chance to disagree with what the checker
            // enforces.
            if info
                .signature
                .ret_ty
                .as_ref()
                .is_some_and(brass_hir::is_fully_known)
            {
                continue;
            }
            let ty = self.function_return_entry(info);
            self.function_returns.insert(name, ty);
        }
    }

    /// The return-table entry for `info`: its annotation when that is fully known,
    /// the light-pass inference when there is none, and -- for a `T!`, which names
    /// only the OK payload -- the annotation with its Err side completed.
    fn function_return_entry(&mut self, info: &FunInfo) -> Type {
        // The light pass resolves names -- a module-qualified call
        // (`percent.decode`), a renamed import, a global -- against the CURRENT
        // module, so the function's own must be current or the lookup misses and
        // the caller loses whatever the callee would have told it.
        let saved = std::mem::replace(&mut self.current_module, info.module.clone());
        let ty = self.function_return_entry_inner(info);
        self.current_module = saved;
        ty
    }

    fn function_return_entry_inner(&mut self, info: &FunInfo) -> Type {
        match &info.signature.ret_ty {
            Some(declared) if brass_hir::is_fully_known(declared) => declared.clone(),
            Some(declared) => {
                let declared = declared.clone();
                let (err, any, generic) =
                    self.body_error_payload(&info.signature.params, &info.decl.body);
                if any {
                    self.error_sites.insert(format!("fn:{}", info.symbol));
                }
                if generic {
                    self.generic_error_returns
                        .insert(format!("fn:{}", info.symbol));
                }
                self.complete_open_error(&declared, err)
            }
            None => self.infer_function_return(&info.signature.params, &info.decl.body),
        }
    }

    /// The Err payload `body` produces, as the light pass reconciles the sites.
    ///
    /// Both shapes count: an `error(..)` / `expr!` PROPAGATION, and a plain
    /// `return` of an already-fallible value -- a body may never propagate and
    /// simply FORWARD a `Result` (`return _plugin_fcall_..(..)`, which is what every
    /// synthesized plugin wrapper does), and the Err it hands back is its own. An
    /// OPEN Err carries no information, so it is dropped rather than allowed to win
    /// the reconciliation against a concrete one.
    fn body_error_payload(
        &mut self,
        params: &[ParamInfo],
        body: &Block,
    ) -> (Option<Type>, bool, bool) {
        let mut env = self.signature_param_env(params);
        // The variables standing for the parameters in THIS light run: an
        // open Err that is one of them is the function's own generic error.
        let param_vars: std::collections::BTreeSet<u32> =
            env.values().flat_map(brass_hir::type_vars).collect();
        let mut normal = Vec::new();
        let mut props = LightProps::default();
        self.infer_returns_block(body, &mut env, &mut normal, &mut props);
        self.error_payload_of(&normal, &props, &param_vars)
    }

    /// The Err payload of a body whose light pass produced `normal` and `props`,
    /// and whether the body had ANY error site at all. See
    /// [`Self::body_error_payload`].
    ///
    /// The two answers differ, and the difference is what makes an unusable `T!`
    /// detectable: NO site is fine (a `T!` whose body never fails still Ok-wraps its
    /// returns, and nothing ever reads the Err), while sites that all come back
    /// UNKNOWN mean the body does propagate an error whose type nothing determines.
    fn error_payload_of(
        &mut self,
        normal: &[(Type, Span)],
        props: &LightProps,
        param_vars: &std::collections::BTreeSet<u32>,
    ) -> (Option<Type>, bool, bool) {
        let mut sites = props.errors.clone();
        for (ty, span) in normal {
            let resolved = self.resolve(ty);
            // The Err slot alone decides: an Err-only construction
            // (`return Result.Err { error: e }`) has no `Ok.value` entry, so
            // `result_payloads` (which demands both) would miss the site. A
            // declared Result subtype counts like the Result itself.
            if let Type::Sum(n) = &resolved
                && self.is_result_like(n)
                && let Some(err) = n.substitution.get(brass_hir::types::RESULT_ERR_ERROR)
            {
                // Forwarded errors are re-raised lifted into the prelude
                // `Error` (see `link_forwarded_error`).
                let lifted = crate::lift_err_payload(self.program, self.resolve(err));
                sites.push((lifted, *span));
            }
        }
        let any = !sites.is_empty();
        // An open err that is one of the SIGNATURE's own variables is a
        // generic error type (`fun wrap(e) -> infer! { return Result.Err {
        // error: e } }`): keeping the variable in the entry ties the err to
        // the parameter, so each call site's instantiation names it. Any
        // other open err carries no information (a body-local variable must
        // not leak into a table shared across call sites) and is dropped.
        let mut generic: Option<Type> = None;
        let known: Vec<(Type, Span)> = sites
            .into_iter()
            .map(|(ty, span)| (self.resolve(&ty), span))
            .filter(|(ty, _)| {
                if let Type::Unknown(v) = ty {
                    if generic.is_none() && param_vars.contains(v) {
                        generic = Some(ty.clone());
                    }
                    return false;
                }
                true
            })
            .collect();
        let reconciled = self.reconcile_error_payloads(&known, false);
        let generic_used = reconciled.is_none() && generic.is_some();
        (reconciled.or(generic), any, generic_used)
    }

    /// Fill the open Err payload of a `T!` return with `err`.
    ///
    /// `T!` names only the OK side; the Err side is inferred from the body's
    /// `error(..)` sites, so the annotation alone describes `Result<T, ?>` -- which
    /// is what a caller reading the signature table, and the editor rendering it,
    /// were left with (`Result<TomlValue, unknown_0>`). Only an OPEN Err is filled,
    /// so an annotation that already names one is never overridden.
    /// Tie the PRECOMPUTED return of an unannotated function to what the full
    /// check inferred for its body.
    ///
    /// Every CALL SITE reads the precomputed entry, and shares its variables. The
    /// light pass that built it cannot do the receiver-scheme parameter pinning the
    /// full check does, so a body that builds a `HashMap.new()` and `set`s into it
    /// leaves the precomputed map's key/value OPEN while the full check pins them.
    /// A recursive function is where that shows: its own body reads the precomputed
    /// entry for the recursive call, and a method called on the map it hands back
    /// (`collect(..)!.pairs()`) then monomorphizes at an open type, which the typed
    /// back end refuses -- a program the checker accepted.
    ///
    /// Only the OK payloads are linked. The `Result`/`?` wrapping is the light
    /// assembly's; the full check's reconciliation does not rebuild it, so unifying
    /// the whole types would fight over the shape rather than fill in the payload.
    /// A conflict is ignored: this only ever REFINES an open variable, and a
    /// genuine disagreement is the light pass's approximation, not a program error.
    pub(super) fn link_inferred_return(&mut self, precomputed: &Type, inferred: &Type) {
        let want = Self::ok_payload(&self.resolve(precomputed));
        let got = Self::ok_payload(&self.resolve(inferred));
        // A body that only ever errors has no Ok value: its payload is a variable no
        // path produces, and unifying with it would say nothing.
        if got.is_unknown() {
            return;
        }
        let _ = self.solver.unify(&want, &got);
    }

    /// A `Result`'s Ok payload, or the type itself when it is not one.
    fn ok_payload(ty: &Type) -> Type {
        ty.result_payloads()
            .map(|(ok, _)| ok.clone())
            .unwrap_or_else(|| ty.clone())
    }

    /// Reject a `T!` whose error type nothing in the body determines.
    ///
    /// `T!` names only the OK payload; the Err type is INFERRED, from the body's
    /// `error(..)` sites and from the `Result`s it forwards. A body with neither
    /// gives inference nothing to work with -- including one whose ONLY propagation
    /// is its own recursive `!`, whose error type is the very variable being
    /// inferred. Left open, the variable reaches the back end, which has no type to
    /// lay the payload out at ("cannot infer the type of an expression temporary").
    /// That is a type error, and it belongs here rather than there.
    ///
    /// Read from the RETURN TABLE, after the passes that fill it: an entry whose Err
    /// is still open is one `complete_open_error` found nothing for. A keyed
    /// `-> infer!` template is exempt -- it has no fixed type at all, being
    /// specialized per call site from the caller's expectation.
    pub(super) fn report_uninferable_error_types(&mut self) {
        let mut open: Vec<Span> = Vec::new();
        for f in self.program.functions.values() {
            if self.seeded_module(&f.module) {
                continue;
            }
            let Some(ret) = self.function_returns.get(&f.symbol) else {
                continue;
            };
            if f.signature.ret_ty.is_some()
                && self.error_sites.contains(&format!("fn:{}", f.symbol))
                && !self
                    .generic_error_returns
                    .contains(&format!("fn:{}", f.symbol))
                && let Some(span) = self.open_error_span(ret, f.decl.ret.as_ref())
            {
                open.push(span);
            }
        }
        for info in self.program.types.values() {
            if self.seeded_module(&info.module) {
                continue;
            }
            let mut method = |qualifier: &str, name: &String, m: &brass_hir::MethodInfo| {
                if brass_hir::keyed_return(m.decl.ret.as_ref()) || m.signature.ret_ty.is_none() {
                    return;
                }
                if !self.error_sites.contains(&format!("m:{qualifier}.{name}"))
                    || self
                        .generic_error_returns
                        .contains(&format!("m:{qualifier}.{name}"))
                {
                    return;
                }
                let key = (qualifier.to_string(), name.clone());
                if let Some(ret) = self.method_returns.get(&key)
                    && let Some(span) = self.open_error_span(ret, m.decl.ret.as_ref())
                {
                    open.push(span);
                }
            };
            match &info.kind {
                TypeKind::Record { methods, .. } => {
                    for (name, m) in methods {
                        method(&info.name, name, m);
                    }
                }
                TypeKind::Sum { variants } => {
                    for v in variants {
                        for (name, m) in &v.methods {
                            method(&format!("{}.{}", info.name, v.name), name, m);
                        }
                    }
                }
            }
        }
        for span in open {
            self.errors.push(TypeError {
                message: "cannot infer the error type of `!`: this body propagates an error \
whose type nothing determines -- the only error it forwards is its own. Raise an `error(..)`, \
or drop the `!`"
                    .to_string(),
                span,
            });
        }
    }

    /// Whether a sum carries the fallibility sugar's shape: the (possibly
    /// shadowing) `Result` itself, or a declared subtype of the `Result` the
    /// current module resolves (or the prelude's).
    fn is_result_like(&self, n: &brass_hir::NominalType) -> bool {
        if n.is_result_type() {
            return true;
        }
        let scoped = self
            .program
            .resolve_type(&self.current_module, brass_hir::RESULT_TYPE_NAME)
            .map(|info| info.id)
            .unwrap_or(brass_hir::RESULT_TYPE_ID);
        crate::structural::declares_sum_parent(self.program, n.id, scoped, 0)
            || crate::structural::declares_sum_parent(
                self.program,
                n.id,
                brass_hir::RESULT_TYPE_ID,
                0,
            )
    }

    /// The span to report a still-open Err payload at, if `ret` has one.
    ///
    /// Resolved through the solver: the full body checks ran before this
    /// report, and a body whose only error source is a FORWARDED callee
    /// Result (`return helper()`) binds its Err variable there rather than in
    /// the light-pass reconciliation the table entry was built from. An err
    /// that is one of the signature's own variables is a GENERIC error type,
    /// named per call site, not an inference failure. Only a variable nothing
    /// binds and nothing ties is genuinely open.
    fn open_error_span(&self, ret: &Type, decl_ret: Option<&TypeExpr>) -> Option<Span> {
        let (_, err) = ret.result_payloads()?;
        if !self.resolve(err).is_unknown() {
            return None;
        }
        Some(decl_ret?.span())
    }

    fn complete_open_error(&mut self, declared: &Type, err: Option<Type>) -> Type {
        let Some(err) = err else {
            return declared.clone();
        };
        let resolved = self.resolve(declared);
        let Some((ok, declared_err)) = resolved.result_payloads() else {
            return declared.clone();
        };
        if !declared_err.is_unknown() {
            return declared.clone();
        }
        // Keep the declared Result's nominal (a scope's shadow included).
        resolved.rebuild_result(ok.clone(), err)
    }

    pub(super) fn precompute_method_returns(&mut self) {
        let mut entries: Vec<(String, String, String, Vec<String>)> = self
            .program
            .types
            .values()
            .flat_map(|info| match &info.kind {
                TypeKind::Record { methods, .. } => methods
                    .keys()
                    .map(|m| {
                        (
                            info.name.clone(),
                            info.name.clone(),
                            m.clone(),
                            info.module.clone(),
                        )
                    })
                    .collect::<Vec<_>>(),
                TypeKind::Sum { variants } => variants
                    .iter()
                    .flat_map(|variant| {
                        variant.methods.keys().map(|m| {
                            (
                                format!("{}.{}", info.name, variant.name),
                                info.name.clone(),
                                m.clone(),
                                info.module.clone(),
                            )
                        })
                    })
                    .collect(),
            })
            .collect();
        entries.sort();
        for (qualifier, self_type, method, module) in entries {
            // A seeded context type's returns are already in the table.
            if self.seeded_module(&module) {
                continue;
            }
            // As in `function_return_entry`: the light pass resolves names against
            // the current module, which here is the TYPE's.
            let saved = std::mem::replace(&mut self.current_module, module);
            let (ty, has_props) = self.infer_method_return(&qualifier, &self_type, &method);
            self.current_module = saved;
            if has_props {
                self.method_return_props
                    .insert((qualifier.clone(), method.clone()));
            }
            self.method_returns.insert((qualifier, method), ty);
        }
    }

    /// The light-pass return type of a method, plus whether its body carries
    /// propagation sites (`error(...)` / nullable `!`) -- when it does, the
    /// light assembly (`Result`/`?` wrapping) is the only correct return shape,
    /// so the co-check's plain reconciliation must not replace it (see the
    /// method-body loop in `infer_program`).
    fn infer_method_return(
        &mut self,
        qualifier: &str,
        self_type: &str,
        method: &str,
    ) -> (Type, bool) {
        let Some(resolved) = self.method_for_qualifier(qualifier, method) else {
            return (self.fresh_unknown(), false);
        };
        let declared = resolved.signature.ret_ty.clone();
        let signature_params = resolved.signature.params.clone();
        let decl = resolved.method;
        // A fully-known annotation IS the return type. A `T!` is not -- it names
        // only the OK payload, leaving the Err side to the body's `error(..)` sites
        // -- so the light pass below runs anyway, purely to complete it. A keyed
        // `-> infer!` template has no fixed type at all (it is specialized per call
        // site from the caller's expectation), so it stays exactly as declared.
        let complete_error = match &declared {
            Some(ty) => {
                if brass_hir::is_fully_known(ty) || brass_hir::keyed_return(decl.ret.as_ref()) {
                    return (ty.clone(), false);
                }
                true
            }
            None => false,
        };
        let Some(body) = &decl.body else {
            return (declared.unwrap_or(Type::Void), false);
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
        let param_vars: std::collections::BTreeSet<u32> =
            env.values().flat_map(brass_hir::type_vars).collect();
        let mut normal = Vec::new();
        let mut props = LightProps::default();
        self.infer_returns_block(body, &mut env, &mut normal, &mut props);
        self.self_type = saved;
        self.self_variant = saved_variant;
        if complete_error {
            let (err_ty, any, generic) = self.error_payload_of(&normal, &props, &param_vars);
            if any {
                self.error_sites.insert(format!("m:{qualifier}.{method}"));
            }
            if generic {
                self.generic_error_returns
                    .insert(format!("m:{qualifier}.{method}"));
            }
            let declared = declared.unwrap_or(Type::Void);
            // The annotation still governs the shape, so this is not a
            // light-assembled return: `has_props` stays false, as for any
            // annotated method.
            return (self.complete_open_error(&declared, err_ty), false);
        }
        let has_props = !props.errors.is_empty() || !props.nulls.is_empty();
        let normal_ty = self.reconcile_return_types(&normal, true);
        let err_ty = self.reconcile_error_payloads(&props.errors, true);
        let base = self.result_from_payloads(normal_ty, err_ty);
        (wrap_null_propagated_return(base, &props.nulls), has_props)
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
        let mut out = HashMap::default();
        for info in self.program.types.values() {
            if let TypeKind::Record { .. } = &info.kind {
                // A seeded context type keeps the scheme the seed carried: its
                // co-check did not run here, so generalizing now would produce
                // an empty shell over nothing.
                if self.seeded_module(&info.module) {
                    if let Some(scheme) = self.schemes.get(&info.name) {
                        out.insert(info.name.clone(), scheme.clone());
                    }
                    continue;
                }
                out.insert(info.name.clone(), self.build_record_scheme(info));
            }
        }
        out
    }

    fn build_record_scheme(&self, info: &TypeInfo) -> TypeScheme {
        let TypeKind::Record { fields, methods } = &info.kind else {
            return TypeScheme::default();
        };
        let mut params: HashSet<u32> = HashSet::default();
        let resolved = |this: &Self, t: Option<&Type>| t.map(|t| this.resolve(t));
        let mut field_types = Vec::with_capacity(fields.len());
        for field in fields {
            let ty = resolved(self, field.resolved_ty.as_ref()).unwrap_or(Type::Void);
            params.extend(self.solver.free_vars(&ty));
            field_types.push((field.name.clone(), ty));
        }
        // The variables the fields are expressed over: the canonical side when a
        // return link aliases a method's own variable to a field's.
        let field_vars: HashSet<u32> = field_types
            .iter()
            .flat_map(|(_, t)| self.solver.free_vars(t))
            .collect();
        let self_ty = info.type_ref();
        let mut scheme_methods = std::collections::BTreeMap::new();
        for (name, method) in methods {
            // Return-path links the co-check recorded for this method: each
            // ties two inference variables that are one type (a parameter
            // returned on one path, a stored field's value on another).
            // Rewrite the aliased variable to its canonical partner --
            // preferring a field variable, so the tie is visible to the
            // instance pinning that resolves scheme parameters from the
            // receiver's fields (`get_or`'s `dflt` becomes the value slot).
            let aliases = self.return_link_aliases(&info.name, name.as_str(), &field_vars);
            let canon = |this: &Self, t: Type| {
                if aliases.is_empty() {
                    t
                } else {
                    brass_hir::substitute_vars(&this.resolve(&t), &aliases)
                }
            };
            let mut ps = Vec::with_capacity(method.signature.params.len());
            for p in &method.signature.params {
                let ty = if p.name == "self" {
                    self_ty.clone()
                } else {
                    canon(
                        self,
                        resolved(self, p.resolved_ty.as_ref()).unwrap_or(Type::Void),
                    )
                };
                params.extend(self.solver.free_vars(&ty));
                ps.push((p.name.clone(), ty));
            }
            // Prefer the return the co-check reconciled in the shared
            // environment: unlike the precomputed light-pass type, it is
            // expressed over the same variables as the fields (a `get` that
            // returns a stored value types as `V?`, not a detached unknown).
            // Absent for propagating bodies, whose `Result`/`?` shape only the
            // light assembly builds -- those keep the precomputed type.
            let ret = self
                .co_method_returns
                .get(&(info.name.clone(), name.clone()))
                .or_else(|| self.method_returns.get(&(info.name.clone(), name.clone())))
                .map(|t| self.resolve(t))
                .or_else(|| resolved(self, method.signature.ret_ty.as_ref()))
                .unwrap_or(Type::Void);
            let ret = canon(self, ret);
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

    /// The variable-alias map a method's recorded return links induce (see
    /// `co_return_links`): for each pair whose two sides resolve to distinct
    /// bare inference variables, the non-canonical one maps to the canonical
    /// -- a variable the type's fields use when either side is one (so the
    /// receiver's field substitution pins it), otherwise the smaller id.
    /// Chained links (`a ~ b`, `b ~ c`) are followed through the map.
    fn return_link_aliases(
        &self,
        type_name: &str,
        method: &str,
        field_vars: &HashSet<u32>,
    ) -> std::collections::BTreeMap<u32, Type> {
        let mut map: std::collections::BTreeMap<u32, Type> = std::collections::BTreeMap::new();
        let Some(links) = self
            .co_return_links
            .get(&(type_name.to_string(), method.to_string()))
        else {
            return map;
        };
        // Follow earlier aliases so chains canonicalize to one variable.
        let chase = |map: &std::collections::BTreeMap<u32, Type>, mut v: u32| loop {
            match map.get(&v) {
                Some(Type::Unknown(next)) => v = *next,
                _ => return v,
            }
        };
        for (a, b) in links {
            let (Type::Unknown(x), Type::Unknown(y)) = (self.resolve(a), self.resolve(b)) else {
                continue;
            };
            let (x, y) = (chase(&map, x), chase(&map, y));
            if x == y {
                continue;
            }
            let canon = if field_vars.contains(&x) {
                x
            } else if field_vars.contains(&y) {
                y
            } else {
                x.min(y)
            };
            let other = if canon == x { y } else { x };
            map.insert(other, Type::Unknown(canon));
        }
        map
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
                    // Keep the forwarded Result's nominal (a shadow included).
                    resolved.rebuild_result(fwd_ok.clone(), merged)
                } else {
                    let span = brass_parser::Span::new(0, 0);
                    self.scoped_result(ok, err, span)
                }
            }
            (Some(ty), None) => ty,
            (None, Some(err)) => {
                let ok = self.fresh_error_only_ok();
                self.scoped_result(ok, err, brass_parser::Span::new(0, 0))
            }
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
        self.reconcile_return_types_with(normal, report, false)
    }

    /// [`Self::reconcile_return_types`] with `link`: the co-check passes true
    /// so that two unifiable return paths are RECORDED as one type for scheme
    /// generalization (see [`Self::co_return_links`]) -- a variable-typed
    /// return (an open parameter, a stored field's value) is tied to its
    /// sibling instead of surviving as an independent scheme parameter.
    /// `HashMap.get_or` returns `e.value` on one path and `dflt` on the
    /// other; without the link `dflt` stayed its own scheme parameter, a call
    /// could pass a string default into an int32-valued map, and the back end
    /// reinterpreted the bits.
    ///
    /// The tie is a side record applied at scheme build, NOT a solver
    /// binding: a commit into the shared persistent solver binds variables
    /// other bodies' cached signature types still reference (the `_Entry`
    /// field variable is program-global), and leaked bindings surfaced as
    /// order-dependent phantom type errors in unrelated functions.
    pub(super) fn reconcile_return_types_with(
        &mut self,
        normal: &[(Type, Span)],
        report: bool,
        link: bool,
    ) -> Option<Type> {
        let (first, rest) = normal.split_first()?;
        let mut common = first.0.clone();
        for (ty, span) in rest {
            if let Some(nullable) = common_nullable_type(&common, ty) {
                common = nullable;
                continue;
            }
            if self.can_unify(&common, ty) {
                if link && let Some(key) = self.current_co_method.clone() {
                    self.co_return_links
                        .entry(key)
                        .or_default()
                        .push((common.clone(), ty.clone()));
                }
                continue;
            }
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

    /// Infer the types of top-level `let`/`const` bindings in module/source order
    /// and record them per DEFINING module. Bindings accumulate as iteration
    /// proceeds, so a later global is never visible to an earlier initializer, and
    /// a module's initializers see only what that module can see (its own globals
    /// so far, its imports', and the stdlib's) -- modules are processed in
    /// dependency order, so an imported module's globals are already inferred.
    /// Annotation resolution errors are surfaced by `resolve_annotations`, so they
    /// are intentionally swallowed here.
    pub(super) fn precompute_global_bindings(&mut self) {
        let program = self.program;
        let mut props = LightProps::default();
        for init in &program.inits {
            // A seeded context module's globals are already in `global_defs`.
            if self.seeded_module(&init.path) {
                continue;
            }
            let mut env = self.globals_visible_from(&init.path);
            let mut own: HashMap<String, Type> = HashMap::default();
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
                self.bind_pattern_light(pat, &binding_ty, &mut own);
            }
            self.global_defs.insert(init.path.clone(), own);
            self.global_scopes.clear();
        }
    }

    /// The globals a body in `module` sees, by the name it sees them under: the
    /// stdlib's (visible everywhere, so `INT64_MAX` needs no import), then the
    /// ones its imports bring in (under the LOCAL name, so a rename resolves),
    /// then its own, which shadow both.
    pub(super) fn globals_visible_from(&self, module: &[String]) -> HashMap<String, Type> {
        let mut out: HashMap<String, Type> = HashMap::default();
        let mut core_paths: Vec<&Vec<String>> = self
            .global_defs
            .keys()
            .filter(|p| p.first().is_some_and(|seg| seg == "core"))
            .collect();
        core_paths.sort();
        for path in core_paths {
            for (name, ty) in &self.global_defs[path] {
                out.entry(name.clone()).or_insert_with(|| ty.clone());
            }
        }
        if let Some(origins) = self.program.import_origins.get(module) {
            let renames = self.program.import_renames.get(module);
            for (local, origin) in origins {
                let remote = renames
                    .and_then(|r| r.get(local))
                    .map(String::as_str)
                    .unwrap_or(local);
                if let Some(ty) = self.global_defs.get(origin).and_then(|g| g.get(remote)) {
                    out.insert(local.clone(), ty.clone());
                }
            }
        }
        if let Some(own) = self.global_defs.get(module) {
            for (name, ty) in own {
                out.insert(name.clone(), ty.clone());
            }
        }
        out
    }

    /// [`Self::globals_visible_from`] for the module being checked, memoized.
    pub(super) fn global_scope(&mut self) -> HashMap<String, Type> {
        let module = self.current_module.clone();
        if let Some(scope) = self.global_scopes.get(&module) {
            return scope.clone();
        }
        let scope = self.globals_visible_from(&module);
        self.global_scopes.insert(module, scope.clone());
        scope
    }

    /// The scope stack used to check a function or method body: the globals
    /// visible from its module at the bottom, signature parameters on top so
    /// parameters shadow same-named globals.
    pub(super) fn signature_scopes(&mut self, params: &[ParamInfo]) -> ScopeStack {
        vec![self.global_scope(), self.signature_param_scope(params)]
    }

    /// A single-scope environment for return inference that layers signature
    /// parameters over the globals, mirroring `signature_scopes` shadowing.
    fn signature_param_env(&mut self, params: &[ParamInfo]) -> HashMap<String, Type> {
        let mut env = self.global_scope();
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
