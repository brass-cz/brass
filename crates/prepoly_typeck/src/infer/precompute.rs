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
            // A fully-known annotation is the declaration itself: re-inferring it
            // would be wasted work and a chance to disagree with what the checker
            // enforces.
            if info
                .signature
                .ret_ty
                .as_ref()
                .is_some_and(prepoly_hir::is_fully_known)
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
        match &info.signature.ret_ty {
            Some(declared) if prepoly_hir::is_fully_known(declared) => declared.clone(),
            Some(declared) => {
                let declared = declared.clone();
                let err = self.body_error_payload(&info.signature.params, &info.decl.body);
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
    fn body_error_payload(&mut self, params: &[ParamInfo], body: &Block) -> Option<Type> {
        let mut env = self.signature_param_env(params);
        let mut normal = Vec::new();
        let mut props = LightProps::default();
        self.infer_returns_block(body, &mut env, &mut normal, &mut props);
        self.error_payload_of(&normal, &props)
    }

    /// The Err payload of a body whose light pass produced `normal` and `props`.
    /// See [`Self::body_error_payload`].
    fn error_payload_of(&mut self, normal: &[(Type, Span)], props: &LightProps) -> Option<Type> {
        let mut sites = props.errors.clone();
        for (ty, span) in normal {
            let resolved = self.resolve(ty);
            if let Some((_, err)) = resolved.result_payloads() {
                sites.push((err.clone(), *span));
            }
        }
        let sites: Vec<(Type, Span)> = sites
            .into_iter()
            .map(|(ty, span)| (self.resolve(&ty), span))
            .filter(|(ty, _)| !ty.is_unknown())
            .collect();
        self.reconcile_error_payloads(&sites, false)
    }

    /// Fill the open Err payload of a `T!` return with `err`.
    ///
    /// `T!` names only the OK side; the Err side is inferred from the body's
    /// `error(..)` sites, so the annotation alone describes `Result<T, ?>` -- which
    /// is what a caller reading the signature table, and the editor rendering it,
    /// were left with (`Result<TomlValue, unknown_0>`). Only an OPEN Err is filled,
    /// so an annotation that already names one is never overridden.
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
        Type::result(ok.clone(), err)
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
            let (ty, has_props) = self.infer_method_return(&qualifier, &self_type, &method);
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
                if prepoly_hir::is_fully_known(ty) || prepoly_hir::keyed_return(decl.ret.as_ref()) {
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
        let mut normal = Vec::new();
        let mut props = LightProps::default();
        self.infer_returns_block(body, &mut env, &mut normal, &mut props);
        self.self_type = saved;
        self.self_variant = saved_variant;
        if complete_error {
            let err_ty = self.error_payload_of(&normal, &props);
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
                    prepoly_hir::substitute_vars(&this.resolve(&t), &aliases)
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
            let mut env = self.globals_visible_from(&init.path);
            let mut own: HashMap<String, Type> = HashMap::new();
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
        let mut out: HashMap<String, Type> = HashMap::new();
        let mut std_paths: Vec<&Vec<String>> = self
            .global_defs
            .keys()
            .filter(|p| p.first().is_some_and(|seg| seg == "std"))
            .collect();
        std_paths.sort();
        for path in std_paths {
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
