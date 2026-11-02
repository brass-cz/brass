//! The tables the body checks start from, and their settlement:
//! duplicate-parameter validation; the precomputed returns of unannotated
//! functions and methods (light walk, with the reconciliation of multiple
//! return and error payloads) and the completed Err side of a `T!`; record
//! type schemes, generalized after the method co-check; the provisional
//! global bindings and the scopes the bodies start from. As the full check
//! reaches each body it settles these entries against what the body really
//! returns or binds (`settle_definitional_return`, `link_inferred_return`,
//! `settle_global`), and a `T!` whose error type nothing determines is
//! reported. The return-table fixpoint is the `fixpoint` submodule.

use super::*;

mod fixpoint;

pub(super) use fixpoint::ReturnKey;

impl<'a> Checker<'a> {
    /// Report every duplicate parameter name of a function or method
    /// signature.
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
            if name != "_" && !seen.insert(name) {
                self.errors.push(TypeError {
                    message: format!("duplicate parameter `{name}` in {owner}"),
                    span,
                });
            }
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
        let param_vars: std::collections::BTreeSet<u32> = env
            .iter()
            .flat_map(|scope| scope.values())
            .flat_map(brass_hir::type_vars)
            .collect();
        let mut normal = Vec::new();
        let mut props = LightProps::default();
        self.infer_returns_block(body, &mut env, &mut normal, &mut props);
        self.error_payload_of(&normal, &props, &param_vars)
    }

    /// The Err payload of a body whose light pass produced `normal` and `props`,
    /// whether the body had ANY error site at all, and whether the payload is
    /// one of the signature's own variables (`param_vars`): a generic error
    /// type. See [`Self::body_error_payload`].
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

    /// Tie the PROVISIONAL return a recursive call was typed against to what
    /// the full check found the body to return (`inferred`), for the
    /// elaboration of `symbol` the call at `span` started.
    ///
    /// The recursive call's result was used inside the body at the provisional
    /// type (see `instance_provisional_return`), so the two must be one type.
    /// Unifying them is what pins a container the body fills: the recursive
    /// call's value is no longer OPEN where it is used. The light pass that
    /// built the provisional type cannot do the receiver-scheme parameter
    /// pinning the full check does, so a body that builds a `HashMap.new()` and
    /// `set`s into it leaves the map's key/value open there while the full
    /// check pins them, and a method called on what the recursion hands back
    /// (`collect(..)!.pairs()`) would otherwise monomorphize at an open type.
    ///
    /// Only the OK payloads are linked. The `Result`/`?` wrapping is the light
    /// assembly's on both sides. A payload the two cannot share means the
    /// recursive call was typed at a type the body does not return: that is
    /// reported, since every use of the call's value was checked against it.
    pub(super) fn link_inferred_return(
        &mut self,
        precomputed: &Type,
        inferred: &Type,
        symbol: &str,
        span: Span,
    ) {
        let want = Self::ok_payload(&self.resolve(precomputed));
        let got = Self::ok_payload(&self.resolve(inferred));
        // A body that only ever errors has no Ok value: its payload is a variable no
        // path produces, and unifying with it would say nothing.
        if got.is_unknown() {
            return;
        }
        let snapshot = self.solver.snapshot();
        if self.solver.unify(&want, &got).is_err() {
            self.solver.rollback(snapshot);
            let name = self
                .program
                .functions
                .get(symbol)
                .map_or(symbol, |f| f.signature.name.as_str());
            self.errors.push(TypeError {
                message: format!(
                    "cannot infer the return type of recursive `{name}`: its recursive call \
                     was typed `{}`, but the body returns `{}`; annotate the return type of \
                     `{name}`",
                    self.resolve(&want).display(),
                    self.resolve(&got).display()
                ),
                span,
            });
        }
    }

    /// Settle a callable's precomputed return `entry` against its definitional
    /// full check, whose `return` types `check_block_root` just collected. The
    /// full check is the authority for the Ok payload; the light pass that built
    /// the entry only approximates it. When the two payloads cannot be one type
    /// the entry's Ok payload is replaced by the full check's (inside the light
    /// assembly's `Result`/`?` shape), and the settled entry is returned. Agreeing
    /// payloads are left alone -- this pass's variables are the signature's own,
    /// shared by every call site, so nothing is unified here.
    pub(super) fn settle_definitional_return(
        &mut self,
        entry: &Type,
        body: &Block,
        collected: Vec<(Type, Span)>,
    ) -> Option<Type> {
        // A type-test body returns a different type per instance; its open
        // definitional walk joins arms no single instance compiles together.
        if block_has_type_test(body) {
            return None;
        }
        let full = self.full_normal_return(collected)?;
        let got = Self::ok_payload(&self.resolve(&full));
        if got.is_unknown() {
            return None;
        }
        let entry = self.resolve(entry);
        let want = Self::ok_payload(&entry);
        // The outer `?` a nullable `!` adds is the light shape's, never part of
        // the value the body returns.
        let peeled = match (&want, &got) {
            (Type::Nullable(inner), got) if !matches!(got, Type::Nullable(_)) => inner.as_ref(),
            _ => &want,
        };
        if self.can_unify(peeled, &got) {
            return None;
        }
        Some(with_ok_payload(&entry, got))
    }

    /// Reject a recursive instantiation of `symbol` at fully-known
    /// `arg_types` whose return `ret` nothing determined: every path returns
    /// another call into the recursion, so the checker has no type to give the
    /// calls and the back end none to compile them at. A `mutual` recursion
    /// went through another callable.
    pub(super) fn report_unsettled_recursive_return(
        &mut self,
        symbol: &str,
        arg_types: &[Type],
        ret: &Type,
        mutual: bool,
        span: Span,
    ) {
        if !arg_types
            .iter()
            .all(|arg| brass_hir::is_fully_known(&self.resolve(arg)))
        {
            return;
        }
        let ret = self.resolve(ret);
        let value = match ret.result_payloads() {
            Some((ok, _)) => ok.clone(),
            None => ret,
        };
        let Type::Unknown(id) = value else {
            return;
        };
        if !matches!(
            self.solver.kind_of(id),
            None | Some(InferenceVarKind::Source)
        ) {
            return;
        }
        let name = self
            .program
            .functions
            .get(symbol)
            .map_or(symbol, |f| f.signature.name.as_str());
        let kind = if mutual { " (mutual recursion)" } else { "" };
        self.errors.push(TypeError {
            message: format!(
                "cannot infer the return type of `{name}`: every value it returns comes from \
                 its own recursion; annotate the return type of `{name}`{kind}"
            ),
            span,
        });
    }

    /// Fill the open Err payload of a `T!` return with `err`.
    ///
    /// `T!` names only the OK side; the Err side is inferred from the body's
    /// `error(..)` sites, so the annotation alone describes `Result<T, ?>`. The
    /// completed entry is what a caller reading the signature table, and the
    /// editor rendering it, see. Only an OPEN Err is filled, so an annotation
    /// that already names one is never overridden.
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

    /// A `Result`'s Ok payload, or the type itself when it is not one.
    pub(super) fn ok_payload(ty: &Type) -> Type {
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
    /// inferred. Left open, the variable would reach the back end, which has no
    /// type to lay the payload out at. That is a type error, and it belongs here.
    ///
    /// Read from the RETURN TABLE, after the passes that fill it: an entry whose Err
    /// is still open is one `complete_open_error` found nothing for. A keyed
    /// `-> infer!` template is exempt -- it has no fixed type at all, being
    /// specialized per call site from the caller's expectation.
    pub(super) fn report_uninferable_error_types(&mut self) {
        for f in self.program.functions.values() {
            self.report_uninferable_function_error_type(f);
        }
        self.report_uninferable_method_error_types();
    }

    /// The check of [`Self::report_uninferable_error_types`] for one function.
    /// The streaming run calls it per body, after the body's inference has
    /// settled and before the body's checked event: a body's return contract
    /// is validated before the consumer may compile it.
    pub(super) fn report_uninferable_function_error_type(&mut self, f: &FunInfo) {
        if !self.selects_body(f.decl.span)
            || self.seeded_module(&f.module)
            || f.signature.ret_ty.is_none()
        {
            return;
        }
        if let Some(ret) = self.function_returns.get(&f.symbol)
            && let Some(span) =
                self.uninferable_error_span(&format!("fn:{}", f.symbol), ret, f.decl.ret.as_ref())
        {
            self.report_uninferable_error_type(span);
        }
    }

    /// The check of [`Self::report_uninferable_error_types`] for every method.
    /// Methods settle together in the co-check, so the streaming run reports
    /// them once, before any body's event is emitted.
    pub(super) fn report_uninferable_method_error_types(&mut self) {
        let mut open: Vec<Span> = Vec::new();
        for info in self.program.types.values() {
            if self.seeded_module(&info.module) {
                continue;
            }
            let mut method = |qualifier: &str, name: &String, m: &brass_hir::MethodInfo| {
                if !self.selects_body(m.decl.span)
                    || brass_hir::keyed_return(m.decl.ret.as_ref())
                    || m.signature.ret_ty.is_none()
                {
                    return;
                }
                let key = (qualifier.to_string(), name.clone());
                if let Some(ret) = self.method_returns.get(&key)
                    && let Some(span) = self.uninferable_error_span(
                        &format!("m:{qualifier}.{name}"),
                        ret,
                        m.decl.ret.as_ref(),
                    )
                {
                    open.push(span);
                }
            };
            match &info.kind {
                TypeKind::Record { methods, .. } => {
                    for (name, m) in methods {
                        method(&info.symbol, name, m);
                    }
                }
                TypeKind::Sum { variants } => {
                    for v in variants {
                        for (name, m) in &v.methods {
                            method(&format!("{}.{}", info.symbol, v.name), name, m);
                        }
                    }
                }
            }
        }
        for span in open {
            self.report_uninferable_error_type(span);
        }
    }

    /// Where to report the uninferable error type of the callable `key`
    /// (`fn:<symbol>` / `m:<qualifier>.<name>`), if it has one: only a
    /// callable with an error site whose Err is not its own generic parameter
    /// (see `generic_error_returns`) and is still open.
    fn uninferable_error_span(
        &self,
        key: &str,
        ret: &Type,
        annotation: Option<&TypeExpr>,
    ) -> Option<Span> {
        if !self.error_sites.contains(key) || self.generic_error_returns.contains(key) {
            return None;
        }
        self.open_error_span(ret, annotation)
    }

    fn report_uninferable_error_type(&mut self, span: Span) {
        self.errors.push(TypeError {
            message: "cannot infer the error type of `!`: this body propagates an error \
whose type nothing determines -- the only error it forwards is its own. Raise an `error(..)`, \
or drop the `!`"
                .to_string(),
            span,
        });
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
    /// the light-pass reconciliation the table entry was built from.
    fn open_error_span(&self, ret: &Type, decl_ret: Option<&TypeExpr>) -> Option<Span> {
        let (_, err) = ret.result_payloads()?;
        if !self.resolve(err).is_unknown() {
            return None;
        }
        Some(decl_ret?.span())
    }

    /// Resolve a table return and renumber its remaining variables so fresh
    /// allocation ids do not look like a semantic change between fixpoint rounds.
    fn canonical_return_shape(&self, ty: &Type) -> Type {
        let resolved = self.resolve(ty);
        let substitution = brass_hir::type_vars(&resolved)
            .into_iter()
            .enumerate()
            .map(|(slot, id)| (id, Type::Unknown(slot as u32)))
            .collect();
        brass_hir::substitute_vars(&resolved, &substitution)
    }

    /// The light-pass return type of a method, plus whether its body carries
    /// propagation sites (`error(...)` / nullable `!`) -- when it does, the
    /// light assembly (`Result`/`?` wrapping) is the only correct return shape,
    /// so the co-check's plain reconciliation must not replace it (see the
    /// method-body loop in `check_method_bodies`).
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
        // `-> infer!` template has no fixed Ok type (it is specialized per call
        // site from the caller's expectation), but every specialization fails
        // with the prelude `Error` wrapping a message, exactly as a keyed call
        // is typed (`check_keyed_method_call`). The entry says so: a caller that
        // propagates the call with `!` has that error type to infer.
        let complete_error = match &declared {
            Some(ty) if brass_hir::keyed_return(decl.ret.as_ref()) => {
                let err = crate::lift_err_payload(self.program, Type::Str);
                return (self.complete_open_error(ty, Some(err)), false);
            }
            Some(ty) => {
                if brass_hir::is_fully_known(ty) {
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
            env.last_mut()
                .expect("signature scope frame")
                .insert("self".to_string(), self.program.types[self_type].type_ref());
        }
        let param_vars: std::collections::BTreeSet<u32> = env
            .iter()
            .flat_map(|scope| scope.values())
            .flat_map(brass_hir::type_vars)
            .collect();
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
        let normal = self.split_forwarded_returns(normal, &mut props);
        let has_props = !props.errors.is_empty() || !props.nulls.is_empty();
        // Type-test and open member-presence arms disagree per instance by
        // design; see `infer_function_return`.
        let report = !block_has_type_test(body) && !props.open_static_test;
        let normal_ty = self.reconcile_return_types(&normal, report);
        let base = self.result_from_payloads(normal_ty, &props.errors, report);
        (wrap_null_propagated_return(base, &props.nulls), has_props)
    }

    /// Generalize every record type into a [`TypeScheme`]. Run after the per-type
    /// method bodies have been checked in one shared environment: that pass binds
    /// `self` to the bare type, so a type's methods share one field variable, and
    /// the bodies' stores/reads link a field's element to the methods' parameter
    /// and return variables (`HashMap`'s entry key/value is the `key`/`value` of
    /// `set`/`_insert` through `self._entries[i] = _Entry { .. }`). This reads the
    /// solver's solution for each field and method signature and quantifies the
    /// inference variables still free across them -- the inferred type parameters.
    pub(super) fn build_schemes(&self) -> HashMap<String, TypeScheme> {
        let mut out = HashMap::default();
        for info in self.program.types.values() {
            if let TypeKind::Record { .. } = &info.kind {
                // A seeded context type keeps the scheme the seed carried: its
                // co-check did not run here, so generalizing now would produce
                // an empty shell over nothing.
                if !self.prepares_scheme(&info.symbol) {
                    continue;
                }
                if self.seeded_scheme(&info.symbol, &info.module) {
                    if let Some(scheme) = self.schemes.get(&info.symbol) {
                        out.insert(info.symbol.clone(), scheme.clone());
                    }
                    continue;
                }
                out.insert(info.symbol.clone(), self.build_record_scheme(info));
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
            debug_assert!(
                (self.preparation.is_none() && self.item_seed.is_none())
                    || method.decl.body.is_none()
                    || brass_hir::keyed_return(method.decl.ret.as_ref())
                    || method
                        .signature
                        .ret_ty
                        .as_ref()
                        .is_some_and(brass_hir::is_fully_known)
                    || self
                        .method_returns
                        .contains_key(&(info.symbol.clone(), name.clone())),
                "record scheme requires an unprepared inferred return: {}.{name}",
                info.symbol
            );
            // Return-path links the co-check recorded for this method: each
            // ties two inference variables that are one type (a parameter
            // returned on one path, a stored field's value on another).
            // Rewrite the aliased variable to its canonical partner --
            // preferring a field variable, so the tie is visible to the
            // instance pinning that resolves scheme parameters from the
            // receiver's fields (`get_or`'s `dflt` becomes the value slot).
            let aliases = self.return_link_aliases(&info.symbol, name.as_str(), &field_vars);
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
                .get(&(info.symbol.clone(), name.clone()))
                .or_else(|| {
                    self.method_returns
                        .get(&(info.symbol.clone(), name.clone()))
                })
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
        // A body with a type test, or a member-presence test on a binding the
        // walk left open, dispatches per instance: its arms may return (and
        // fail with) different types, one per instantiation, so the OPEN
        // definitional walk -- which cannot select an arm -- must not report
        // their disagreement. Each instance reconciles its own live path.
        let report = !block_has_type_test(body) && !props.open_static_test;
        let normal = self.split_forwarded_returns(normal, &mut props);
        let normal_ty = self.reconcile_return_types(&normal, report);
        let base = self.result_from_payloads(normal_ty, &props.errors, report);
        wrap_null_propagated_return(base, &props.nulls)
    }

    /// Classify the value returns of a FALLIBLE body (one with an error site,
    /// or a `!` on an operand the walk could not type) that mixes forwarded
    /// `Result`s with bare values. In such a body `return v` Ok-wraps a bare
    /// value and passes a `Result` through whole (types.md, Result), so the two
    /// meet at the Ok payload: each forwarded Result contributes its Ok payload
    /// to the value returns and its Err payload to the error sites. A body that
    /// only forwards is assembled whole by `result_from_payloads`, and a body
    /// without an error site is not fallible, so mixing there stays an
    /// incompatible-return error.
    pub(super) fn split_forwarded_returns(
        &self,
        normal: Vec<(Type, Span)>,
        props: &mut LightProps,
    ) -> Vec<(Type, Span)> {
        if props.errors.is_empty() && !props.open_errors {
            return normal;
        }
        let forwards = normal
            .iter()
            .filter(|(ty, _)| self.resolve(ty).result_payloads().is_some())
            .count();
        if forwards == 0 || forwards == normal.len() {
            return normal;
        }
        normal
            .into_iter()
            .map(|(ty, span)| match self.resolve(&ty).result_payloads() {
                Some((ok, err)) => {
                    props.errors.push((err.clone(), span));
                    (ok.clone(), span)
                }
                None => (ty, span),
            })
            .collect()
    }

    /// Combine the inferred normal (Ok) and error (Err) return payloads into a
    /// single return type. A function that only ever returns via `error(..)` /
    /// propagation still has an inferred `Ok` payload as a fresh unknown.
    ///
    /// A normal payload that is itself a `Result` is forwarded whole, never
    /// nested: the back ends Ok-wrap only bare return values (an
    /// already-fallible value passes through), so a nested
    /// `Result<Result<T>>` here would describe a value the program never
    /// builds. This mirrors the annotated-return path, which flows
    /// `Result`-typed values whole (see `check_return`).
    pub(super) fn result_from_payloads(
        &mut self,
        normal_ty: Option<Type>,
        errors: &[(Type, Span)],
        report: bool,
    ) -> Type {
        match normal_ty {
            Some(ok) => {
                let resolved = self.resolve(&ok);
                if let Some((fwd_ok, fwd_err)) = resolved.result_payloads() {
                    // The forwarded Result's error payload and the body's own
                    // error sites must describe one type. Put the forwarded
                    // payload first so a conflict is attributed to the concrete
                    // local site's span and recovery retains the forwarded shape.
                    if errors.is_empty() {
                        return ok;
                    }
                    let mut payloads = Vec::with_capacity(errors.len() + 1);
                    payloads.push((fwd_err.clone(), Span::new(0, 0)));
                    payloads.extend(errors.iter().cloned());
                    let merged = self
                        .reconcile_error_payloads(&payloads, report)
                        .map(|ty| self.resolve(&ty))
                        .unwrap_or_else(|| fwd_err.clone());
                    // Keep the forwarded Result's nominal (a shadow included).
                    resolved.rebuild_result(fwd_ok.clone(), merged)
                } else if let Some(err) = self.reconcile_error_payloads(errors, report) {
                    let span = brass_parser::Span::new(0, 0);
                    self.scoped_result(ok, err, span)
                } else {
                    ok
                }
            }
            None => {
                if let Some(err) = self.reconcile_error_payloads(errors, report) {
                    let ok = self.fresh_error_only_ok();
                    self.scoped_result(ok, err, brass_parser::Span::new(0, 0))
                } else {
                    Type::Void
                }
            }
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
    /// other; without the link `dflt` would stay its own scheme parameter,
    /// and a call could pass a string default into an `int32`-valued map.
    ///
    /// The tie is a side record applied at scheme build, NOT a solver
    /// binding: a commit into the shared persistent solver would bind
    /// variables other bodies' cached signature types still reference (the
    /// `_Entry` field variable is program-global), constraining unrelated
    /// functions.
    pub(super) fn reconcile_return_types_with(
        &mut self,
        normal: &[(Type, Span)],
        report: bool,
        link: bool,
    ) -> Option<Type> {
        let first = normal.first()?;
        // A fully-known set (an instantiation, or a definition whose returns
        // do not depend on open parameters) joins by the shared value join:
        // numeric widening, literal adaptation, nullable and sum-parent
        // rules, independent of the order of the returns.
        if let Some(joined) = self.join_known_values(normal) {
            return match joined {
                Ok(ty) => ty,
                Err(conflict) => {
                    if report {
                        self.report_join_conflict("return types", normal, conflict);
                    }
                    // Keep the first type so callers check against a
                    // definite type rather than cascading a second error.
                    Some(first.0.clone())
                }
            };
        }
        // An open set. A numeric literal return adapts to whatever the other
        // returns join at, so when one returns a still-open closure parameter
        // (typed by each application) the common type is taken from it --
        // otherwise `return 0` written before `return x` would fix `x` to
        // `int32` for every application.
        let lead = normal
            .iter()
            .position(|(ty, _)| {
                matches!(self.resolve(ty), Type::Unknown(id) if self.closure_param_vars.contains(&id))
            })
            .filter(|_| {
                normal
                    .iter()
                    .any(|(_, span)| self.return_literals.contains_key(span))
            })
            .unwrap_or(0);
        let mut common = normal[lead].0.clone();
        let others = normal[..lead].iter().chain(&normal[lead + 1..]);
        for (ty, span) in others {
            if let Some(nullable) = common_nullable_type(&common, ty) {
                common = nullable;
                continue;
            }
            if self.can_unify(&common, ty) {
                if link && self.current_co_method.is_some() {
                    self.record_co_return_link(common.clone(), ty.clone());
                }
                continue;
            }
            if report {
                let message = format!(
                    "incompatible return types: `{}` and `{}`",
                    self.resolve(&common).display(),
                    self.resolve(ty).display()
                );
                self.report_conflict_once("return types", message, *span);
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
        // A fully-known set joins by the shared value join (see
        // `reconcile_return_types_with`).
        if let Some(joined) = self.join_known_values(errors) {
            return match joined {
                Ok(ty) => ty,
                Err(conflict) => {
                    if report {
                        self.report_join_conflict("error payloads", errors, conflict);
                    }
                    Some(first.0.clone())
                }
            };
        }
        let mut common = first.0.clone();
        for (ty, span) in rest {
            if let Some(nullable) = common_nullable_type(&common, ty) {
                common = nullable;
                continue;
            }
            if !self.can_unify(&common, ty) {
                if report {
                    let message = format!(
                        "incompatible error payloads: `{}` and `{}`",
                        self.resolve(&common).display(),
                        self.resolve(ty).display()
                    );
                    self.report_conflict_once("error payloads", message, *span);
                }
                return Some(common);
            }
        }
        Some(common)
    }

    pub(super) fn param_scope(&mut self, params: &[Param]) -> HashMap<String, Type> {
        params
            .iter()
            .filter(|p| p.name != "_")
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
            .filter(|p| p.name != "_")
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
    /// so far, its imports', and the prelude's) -- modules are processed in
    /// dependency order, so an imported module's globals are already inferred.
    /// Annotation resolution errors are surfaced by `resolve_annotations`, so they
    /// are intentionally swallowed here.
    ///
    /// These are PROVISIONAL types: the full check of each module initializer
    /// is the authority, and replaces each entry as soon as the binding's own
    /// statement is checked (see `settle_global`). Until then the bodies
    /// checked before the initializers -- the method co-check -- and the
    /// light return inference read these.
    pub(super) fn precompute_global_bindings(&mut self) {
        let program = self.program;
        let mut props = LightProps::default();
        for init in &program.inits {
            // A seeded context module's globals are already in `global_defs`.
            if self.seeded_globals(&init.path) {
                continue;
            }
            // Annotations and names resolve in the initializer's own module.
            let saved = std::mem::replace(&mut self.current_module, init.path.clone());
            let mut env = vec![Scope::new(self.globals_visible_from(&init.path))];
            let mut own = vec![Scope::default()];
            for stmt in &init.stmts {
                let Stmt::Let {
                    pat,
                    ty,
                    value,
                    is_const,
                    ..
                } = stmt
                else {
                    continue;
                };
                if value.is_none() {
                    // A module-level binding is a global initialized by the
                    // module's init; without an initializer there is no init
                    // order at which it becomes defined.
                    self.errors.push(TypeError {
                        message: "a top-level `let` needs an initializer".to_string(),
                        span: stmt.span(),
                    });
                    continue;
                }
                let binding_ty =
                    self.light_let_type(ty.as_ref(), value.as_ref(), *is_const, &env, &mut props);
                self.bind_pattern_light(pat, &binding_ty, &mut env);
                self.bind_pattern_light(pat, &binding_ty, &mut own);
            }
            self.current_module = saved;
            self.global_defs.insert(
                init.path.clone(),
                own.pop().expect("global scope frame").into_map(),
            );
            self.global_scopes.clear();
        }
    }

    /// Make the full check's type of the global `name` of `module` -- the
    /// binding its initializer statement just bound -- the type every later
    /// body reads. The provisional (light) entry is unified with it first, so
    /// whatever already shares the entry's variables (a light return that
    /// hands the global back, a container's element slots) follows; a
    /// method body co-checked against an entry the full check contradicts was
    /// checked at the wrong type, which is reported.
    pub(super) fn settle_global(&mut self, module: &[String], name: &str, full: &Type, span: Span) {
        let Some(light) = self
            .global_defs
            .get(module)
            .and_then(|g| g.get(name))
            .cloned()
        else {
            return;
        };
        let snapshot = self.solver.snapshot();
        if self.solver.unify(&light, full).is_err() {
            self.solver.rollback(snapshot);
            if self.co_global_reads.contains(name) {
                self.errors.push(TypeError {
                    message: format!(
                        "global `{name}` has type `{}`, but a method reading it was checked \
                         when it was only known as `{}`; annotate `{name}`",
                        self.resolve(full).display(),
                        self.resolve(&light).display()
                    ),
                    span,
                });
            }
        }
        if let Some(globals) = self.global_defs.get_mut(module) {
            globals.insert(name.to_string(), full.clone());
        }
        self.global_scopes.clear();
    }

    /// The globals a body in `module` sees, by the name it sees them under: the
    /// prelude's (`core` modules, visible everywhere, so `INT64_MAX` needs no
    /// import), then the ones its imports bring in (under the LOCAL name, so a
    /// rename resolves), then its own, which shadow both.
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
    pub(super) fn global_scope(&mut self) -> Rc<HashMap<String, Type>> {
        let module = self.current_module.clone();
        if let Some(scope) = self.global_scopes.get(&module) {
            return Rc::clone(scope);
        }
        let scope = Rc::new(self.globals_visible_from(&module));
        self.global_scopes.insert(module, Rc::clone(&scope));
        scope
    }

    /// The scope stack used to check a function or method body: the globals
    /// visible from its module at the bottom, signature parameters on top so
    /// parameters shadow same-named globals.
    pub(super) fn signature_scopes(&mut self, params: &[ParamInfo]) -> ScopeStack {
        vec![
            Scope::shared(self.global_scope()),
            Scope::new(self.signature_param_scope(params)),
        ]
    }

    /// [`Self::signature_scopes`], as the environment of the light return
    /// inference.
    fn signature_param_env(&mut self, params: &[ParamInfo]) -> ScopeStack {
        self.signature_scopes(params)
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

/// A light-assembled return `shape` -- a payload, a `Result` over it, either
/// one under the outer `?` a nullable `!` adds -- with its Ok payload replaced
/// by `ok`.
fn with_ok_payload(shape: &Type, ok: Type) -> Type {
    match shape {
        Type::Nullable(inner) if inner.result_payloads().is_some() => {
            Type::Nullable(Box::new(with_ok_payload(inner, ok)))
        }
        Type::Nullable(_) => Type::nullable(ok),
        result => match result.result_payloads() {
            Some((_, err)) => result.rebuild_result(ok, err.clone()),
            None => ok,
        },
    }
}

/// Whether `b` contains a type-test `if` condition anywhere. Such a body
/// dispatches per instance, so the open definitional walk reconciles its
/// returns leniently (see `infer_function_return`).
pub(super) fn block_has_type_test(b: &Block) -> bool {
    struct Finder(bool);
    impl crate::walk::ExprVisitor for Finder {
        fn visit(&mut self, e: &Expr) {
            if matches!(e, Expr::TypeTest(..)) {
                self.0 = true;
            }
        }
    }
    let mut finder = Finder(false);
    crate::walk::walk_block(b, &mut finder);
    finder.0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn same_named_receivers_have_distinct_light_returns() {
        // Inspect the precomputed table itself so call-site re-inference cannot
        // conceal unknown or cross-module return entries.
        let modules =
            [("a", "int32"), ("b", "string")].map(|(module, ty)| brass_hir::LoadedModule {
                source: None,
                is_prelude: false,
                path: vec![module.into()],
                ast: brass_parser::parse(&format!(
                    "type Item = {{ value: {ty} }}\nfun Item.get(self) {{ return self.value }}\nfun Item.forward(self) {{ return self.get() }}"
                ))
                .unwrap(),
            });
        let (program, errors) = brass_hir::lower(&modules);
        assert!(errors.is_empty());
        let mut checker =
            Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
        checker.precompute_returns();
        assert!(checker.errors.is_empty());
        assert_eq!(
            checker.method_returns[&("Item@a".into(), "get".into())],
            Type::Int(IntKind::I32)
        );
        assert_eq!(
            checker.method_returns[&("Item@b".into(), "get".into())],
            Type::Str
        );
        assert_eq!(
            checker.method_returns[&("Item@a".into(), "forward".into())],
            Type::Int(IntKind::I32)
        );
        assert_eq!(
            checker.method_returns[&("Item@b".into(), "forward".into())],
            Type::Str
        );
        let schemes = checker.build_schemes();
        assert!(schemes.contains_key("Item@a"));
        assert!(schemes.contains_key("Item@b"));
    }

    #[test]
    fn a_caller_of_prelude_input_takes_its_declared_return() {
        // The light pass types a call of the prelude's `input` by the
        // prelude declaration's (inferred) return -- its Err is the prelude
        // `Error` -- not by the builtin stand-in used without a prelude.
        let prelude = |name: &str, src: &str| brass_hir::LoadedModule {
            source: None,
            is_prelude: true,
            path: vec!["core".into(), name.into()],
            ast: brass_parser::parse(src).unwrap(),
        };
        let modules = [
            prelude("error", include_str!("../../../../core/error.cz")),
            prelude("io", include_str!("../../../../core/io.cz")),
            brass_hir::LoadedModule {
                source: None,
                is_prelude: false,
                path: vec!["main".into()],
                ast: brass_parser::parse("fun ask() { return input() }").unwrap(),
            },
        ];
        let (program, errors) = brass_hir::lower(&modules);
        assert!(errors.is_empty(), "{errors:?}");
        let mut checker =
            Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
        checker.precompute_returns();
        let input = checker.resolve(&checker.function_returns["input"]);
        let ask = checker.resolve(&checker.function_returns["ask"]);
        let (_, input_err) = input.result_payloads().expect("input is fallible");
        let (_, ask_err) = ask.result_payloads().expect("ask forwards input's Result");
        assert!(
            matches!(input_err, Type::Record(n) if n.name == "Error"),
            "{}",
            input.display()
        );
        assert_eq!(ask_err.display(), input_err.display());
    }

    #[test]
    fn failed_inferred_return_link_rolls_back_partial_bindings() {
        let program = Program::empty();
        let mut checker =
            Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
        let open = checker.fresh_unknown();
        let precomputed = Type::Tuple(vec![open.clone(), Type::Str]);
        let inferred = Type::Tuple(vec![Type::Bool, Type::Int(IntKind::I32)]);

        checker.link_inferred_return(&precomputed, &inferred, "f", Span::new(3, 4));

        // A later component mismatch must undo the earlier component binding
        // instead of poisoning the shared solver, and the disagreement between
        // the recursive call's type and the body's return is reported.
        assert!(checker.resolve(&open).is_unknown());
        assert_eq!(checker.errors.len(), 1);
        assert!(
            checker.errors[0]
                .message
                .contains("cannot infer the return type of recursive `f`")
        );
    }

    #[test]
    fn forwarded_and_local_error_payloads_must_reconcile() {
        let program = Program::empty();
        let mut checker =
            Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
        let local_span = Span::new(10, 12);
        let forwarded = Type::result(Type::Int(IntKind::I32), Type::Str);

        checker.result_from_payloads(Some(forwarded), &[(Type::Bool, local_span)], true);

        // A concrete local error cannot be silently discarded in favor of the
        // forwarded Result; the disagreement is reported at the local site.
        assert!(checker.errors.iter().any(|error| {
            error.span == local_span && error.message.contains("incompatible error payloads")
        }));
    }
}
