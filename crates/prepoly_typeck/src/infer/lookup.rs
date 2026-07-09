//! Name, method, and module-visibility lookup: resolving methods for a
//! receiver type, static call qualifiers, functions and imports across
//! module boundaries, and `Self`/type-symbol naming. Also owns the
//! shape constraints recorded on inference variables, verified here
//! against the capabilities the solved type actually exposes.

use super::*;

impl<'a> Checker<'a> {
    pub(super) fn methods_for_type(&self, ty: &Type, method: &str) -> Option<Vec<ResolvedMethod>> {
        // Mode wrappers expose the underlying value's methods: a call through a
        // `ref(mut(T))` parameter must resolve (and type-check its arguments
        // against) `T`'s methods rather than deferring to runtime dispatch.
        match prepoly_hir::peel_modes(&self.resolve(ty)).clone() {
            Type::Record(name) => {
                // Resolve by the receiver's unique id, and key the resolved
                // method on the type's symbol so dispatch is correct when two
                // modules share a type name.
                let info = self.program.type_by_id(name.id)?;
                let TypeKind::Record { methods, .. } = &info.kind else {
                    return None;
                };
                let m = methods.get(method)?;
                let resolved = ResolvedMethod {
                    qualifier: info.symbol.clone(),
                    self_type: info.symbol.clone(),
                    signature: m.signature.clone(),
                    method: m.decl.as_ref().clone(),
                };
                Some(vec![apply_method_substitution(
                    resolved,
                    &name.substitution,
                    method,
                )])
            }
            Type::Sum(name) => {
                let info = self.program.type_by_id(name.id)?;
                let TypeKind::Sum { variants } = &info.kind else {
                    return None;
                };
                if variants.is_empty() {
                    return None;
                }
                let methods = variants
                    .iter()
                    .map(|variant| {
                        let method = variant.methods.get(method)?;
                        Some(ResolvedMethod {
                            qualifier: format!("{}.{}", info.symbol, variant.name),
                            self_type: info.symbol.clone(),
                            signature: method.signature.clone(),
                            method: method.decl.as_ref().clone(),
                        })
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(methods)
            }
            _ => None,
        }
    }

    pub(super) fn method_for_qualifier(
        &self,
        qualifier: &str,
        method: &str,
    ) -> Option<ResolvedMethod> {
        // `Sum.Variant.method()`: only when the first segment is actually a
        // type (not a module alias producing a marker like `"vec.Vec2"`).
        if let Some((sum, variant)) = qualifier.split_once('.')
            && let Some(symbol) = self.resolve_type_symbol(sum)
        {
            let info = self.program.types.get(&symbol)?;
            if let Some(v_method) = info.variant(variant).and_then(|v| v.methods.get(method)) {
                return Some(ResolvedMethod {
                    qualifier: format!("{symbol}.{variant}"),
                    self_type: symbol.clone(),
                    signature: v_method.signature.clone(),
                    method: v_method.decl.as_ref().clone(),
                });
            }
        }
        let type_name = self.resolve_self_name(qualifier);
        let symbol = self.resolve_type_symbol(&type_name)?;
        let TypeKind::Record { methods, .. } = &self.program.types.get(&symbol)?.kind else {
            return None;
        };
        let type_name = symbol;
        let method = methods.get(method)?;
        Some(ResolvedMethod {
            qualifier: type_name.clone(),
            self_type: type_name,
            signature: method.signature.clone(),
            method: method.decl.as_ref().clone(),
        })
    }

    pub(super) fn check_common_method_signatures(
        &mut self,
        methods: &[ResolvedMethod],
        method: &str,
        span: prepoly_parser::Span,
    ) {
        let Some((first, rest)) = methods.split_first() else {
            return;
        };
        for other in rest {
            if !crate::structural::signature_satisfies(
                self.program,
                &other.signature,
                &first.signature,
            ) || !crate::structural::signature_satisfies(
                self.program,
                &first.signature,
                &other.signature,
            ) {
                self.errors.push(TypeError {
                    message: format!(
                        "variant method `{method}` has incompatible signatures in `{}` and `{}`",
                        first.qualifier, other.qualifier
                    ),
                    span,
                });
            }
        }
    }

    pub(super) fn static_qualifier(&self, expr: &Expr, scopes: &ScopeStack) -> Option<String> {
        match expr {
            Expr::Ident(name, _)
                if self.lookup(scopes, name).is_none() && self.is_type_word(name) =>
            {
                Some(self.resolve_self_name(name))
            }
            // `typeof(v).method(..)`: `typeof(v)` names v's static type, so it is
            // a static-call qualifier -- `typeof(v).from(x)` calls the `from` of
            // v's type. The receiver's type must already be resolved to a
            // nominal (or primitive) here; an open type has no name yet.
            Expr::Call(callee, args, _) if matches!(&**callee, Expr::Ident(n, _) if n == "typeof") =>
            {
                let [arg] = args.as_slice() else {
                    return None;
                };
                let ty = self.static_arg_type(&arg.expr, scopes)?;
                match prepoly_hir::peel_modes(&self.resolve(&ty)) {
                    Type::Record(n) | Type::Sum(n) => Some(n.name.clone()),
                    Type::Unknown(_) => None,
                    other => Some(other.type_name()),
                }
            }
            Expr::Field(base, variant, _) => {
                let Expr::Ident(type_name, _) = &**base else {
                    return None;
                };
                if self.lookup(scopes, type_name).is_some() {
                    return None;
                }
                let resolved = self.resolve_self_name(type_name);
                let info = self
                    .program
                    .types
                    .get(&resolved)
                    .or_else(|| self.program.resolve_type(&self.current_module, &resolved));
                info.and_then(|i| i.variant(variant))
                    .map(|_| format!("{resolved}.{variant}"))
            }
            _ => None,
        }
    }

    pub(super) fn lookup(&self, scopes: &ScopeStack, name: &str) -> Option<Type> {
        scopes.iter().rev().find_map(|s| s.get(name).cloned())
    }

    /// The type of a `typeof(arg)` argument for static-qualifier resolution,
    /// looked up without inference (so this stays `&self`): a bound variable's
    /// type, or `self`'s. A general expression has no already-known type here
    /// and is not a static qualifier.
    fn static_arg_type(&self, arg: &Expr, scopes: &ScopeStack) -> Option<Type> {
        match arg {
            Expr::Ident(name, _) => self.lookup(scopes, name),
            Expr::SelfExpr(_) => self.lookup(scopes, "self"),
            _ => None,
        }
    }

    /// Whether `name` denotes a legitimate value that needs no local binding: a
    /// free function visible from the current module or a runtime builtin. Used
    /// by name resolution to distinguish an undeclared identifier from a
    /// function or builtin referenced before/without a local binding. Type words
    /// and unit variants are intentionally excluded here; their value forms are
    /// `Type.method`/`Type.Variant` field accesses, not bare identifiers.
    pub(super) fn is_resolvable_free_name(&self, name: &str) -> bool {
        self.is_function_visible(name) || is_runtime_builtin_value(name)
    }

    /// Whether a program free function `name` is visible from the module being
    /// checked: defined in that module, implicitly imported as
    /// part of the standard-library prelude, or brought in by an `import`.
    fn is_function_visible(&self, name: &str) -> bool {
        self.lookup_function(name).is_some()
    }

    /// Resolve a bare free-function name to its definition from the current
    /// module. A name defined in a single module keeps
    /// its bare symbol, so the common case is a direct map hit gated by
    /// visibility. A name defined in several modules has only module-qualified
    /// symbols, so resolution prefers this module's own definition, then the one
    /// brought in by an `import`.
    pub(super) fn lookup_function(&self, name: &str) -> Option<&prepoly_hir::FunInfo> {
        // A dotted marker from the qualified-use rewrite: resolve through the
        // alias table directly; visibility is already validated by the pass.
        if name.contains('.') {
            return self.program.resolve_function(&self.current_module, name);
        }
        // A renamed import: the local name is only this module's alias for the
        // origin's remote name, so it must not fall through to the bare table,
        // where an unrelated module's function of the same name would capture
        // it. Renames colliding with local declarations are rejected upstream.
        if let Some(remote) = self.import_remote(name) {
            let origin = self.import_origin(name)?;
            return self
                .program
                .functions
                .get(&prepoly_hir::qualify(remote, origin))
                .or_else(|| self.program.functions.get(remote));
        }
        if let Some(info) = self.program.functions.get(name) {
            return self
                .is_module_name_visible(&info.module, name)
                .then_some(info);
        }
        if let Some(info) = self
            .program
            .functions
            .get(&prepoly_hir::qualify(name, &self.current_module))
        {
            return Some(info);
        }
        let origin = self.import_origin(name)?;
        self.program
            .functions
            .get(&prepoly_hir::qualify(name, origin))
    }

    /// The origin module path of an imported local name in the current module.
    fn import_origin(&self, name: &str) -> Option<&[String]> {
        self.program
            .import_origins
            .get(&self.current_module)?
            .get(name)
            .map(Vec::as_slice)
    }

    /// The remote (original) name for an imported local name in the current
    /// module, or `None` when there is no rename.
    fn import_remote(&self, name: &str) -> Option<&str> {
        self.program
            .import_renames
            .get(&self.current_module)
            .and_then(|m| m.get(name))
            .map(String::as_str)
    }

    /// The per-module visibility rule shared by functions and types: a name
    /// declared in `defining` is visible from `current_module` when it is the
    /// same module, a compiler builtin (empty module path, e.g. `Result`), a
    /// public standard-library name (implicit prelude), or
    /// explicitly imported into the current module FROM `defining` under this
    /// very name. An import of the same name from a different module, or a
    /// rename whose local happens to equal `name`, does not make this
    /// definition visible.
    pub(super) fn is_module_name_visible(&self, defining: &[String], name: &str) -> bool {
        if defining == self.current_module.as_slice() || defining.is_empty() {
            return true;
        }
        // Only the implicit-prelude modules are visible with no import; the
        // nested standard-library modules (`std.net`, ...) follow the same
        // import rule as user modules.
        if self.program.prelude_modules.contains(defining) && !name.starts_with('_') {
            return true;
        }
        self.import_remote(name).is_none()
            && self
                .import_origin(name)
                .is_some_and(|origin| origin == defining)
    }

    /// Whether the nominal type declared in `defining` as `name` can be named
    /// from the current module: same module, builtin, std prelude, or imported
    /// under ANY local name -- an `as` rename still makes the type itself
    /// nameable here, just under its local alias. Structural method dispatch
    /// uses this: adoption is gated on the author having named the type in
    /// this module, whatever they named it.
    pub(super) fn is_nominal_visible(&self, defining: &[String], name: &str) -> bool {
        if defining == self.current_module.as_slice() || defining.is_empty() {
            return true;
        }
        // Prelude only, as in `is_module_name_visible`.
        if self.program.prelude_modules.contains(defining) && !name.starts_with('_') {
            return true;
        }
        let Some(origins) = self.program.import_origins.get(&self.current_module) else {
            return false;
        };
        origins.iter().any(|(local, origin)| {
            origin.as_slice() == defining
                && self.import_remote(local).unwrap_or(local.as_str()) == name
        })
    }

    /// Switch `current_module` to the module chosen by `pick` for the duration
    /// of a re-checked callee body, returning the previous module to restore.
    /// A `None` pick leaves the module unchanged.
    pub(super) fn swap_module_for(
        &mut self,
        pick: impl FnOnce(&Program) -> Option<Vec<String>>,
    ) -> Vec<String> {
        match pick(self.program) {
            Some(module) => std::mem::replace(&mut self.current_module, module),
            None => self.current_module.clone(),
        }
    }

    /// Record a deferred structural constraint on `ty` if it resolves to an
    /// inference variable. Used while checking a closure body that operates on
    /// an unknown-typed parameter; the constraint is verified when the variable
    /// is solved at a call site (see `crate::constraint`).
    pub(super) fn record_shape(&mut self, ty: &Type, constraint: ShapeConstraint) {
        if let Type::Unknown(id) = self.resolve(ty) {
            self.shape_constraints
                .entry(id)
                .or_default()
                .push(constraint);
        }
    }

    /// Record an equality constraint for an unknown operand when the operator
    /// needs an exact non-convertible type. Numeric operands are resolved at the
    /// call site through the common numeric type, so this mainly preserves
    /// constraints such as string concatenation.
    pub(super) fn record_binary_shape(&mut self, op: BinOp, left: &Type, right: &Type) {
        let same_typed = matches!(
            op,
            BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::Div
                | BinOp::Rem
                | BinOp::Lt
                | BinOp::Gt
                | BinOp::Le
                | BinOp::Ge
                | BinOp::BitAnd
                | BinOp::BitOr
                | BinOp::BitXor
                | BinOp::Shl
                | BinOp::Shr
        );
        if !same_typed {
            return;
        }
        let is_operand = |t: &Type| matches!(t, Type::Int(_) | Type::Float(_) | Type::Str);
        match (left, right) {
            (Type::Unknown(_), other) if is_operand(other) => {
                self.record_shape(left, ShapeConstraint::Equals(other.clone()));
            }
            (other, Type::Unknown(_)) if is_operand(other) => {
                self.record_shape(right, ShapeConstraint::Equals(other.clone()));
            }
            _ => {}
        }
    }

    /// Verify the constraints recorded for the inference variable `var` against
    /// the concrete type `got` it has been solved to at a call site. A `got`
    /// that is still unknown is skipped (the requirement stays deferred).
    pub(super) fn verify_shape_constraints(
        &mut self,
        var: &Type,
        got: &Type,
        span: prepoly_parser::Span,
    ) {
        let Type::Unknown(id) = self.resolve(var) else {
            return;
        };
        let got = self.resolve(got);
        if matches!(got, Type::Unknown(_)) {
            return;
        }
        let Some(constraints) = self.shape_constraints.get(&id).cloned() else {
            return;
        };
        for constraint in constraints {
            match constraint {
                ShapeConstraint::Equals(expected) => {
                    if !self.can_unify(&got, &expected) {
                        self.errors.push(TypeError {
                            message: format!(
                                "cannot use `{}` where `{}` is required",
                                got.display(),
                                expected.display()
                            ),
                            span,
                        });
                    }
                }
                ShapeConstraint::HasMethod(name) => {
                    if !self.concrete_type_has_method(&got, &name) {
                        self.errors.push(TypeError {
                            message: format!("`{}` has no method `{name}`", got.display()),
                            span,
                        });
                    }
                }
                ShapeConstraint::HasField(name) => {
                    if !self.concrete_type_has_field(&got, &name) {
                        self.errors.push(TypeError {
                            message: format!("`{}` has no field `{name}`", got.display()),
                            span,
                        });
                    }
                }
                ShapeConstraint::Indexable => {
                    if !matches!(got, Type::Array(_, _) | Type::Slice(_) | Type::Str) {
                        self.errors.push(TypeError {
                            message: format!("cannot index `{}`", got.display()),
                            span,
                        });
                    }
                }
            }
        }
    }

    /// Whether a resolved concrete type definitely exposes a callable method,
    /// considering user methods, builtin collection/file/string methods, and
    /// UFCS free functions. Conservative: a non-concrete type (an unsolved
    /// variable, nullable, function, ...) returns `true` so only a method that
    /// is genuinely absent on a concrete receiver is rejected.
    fn concrete_type_has_method(&self, ty: &Type, method: &str) -> bool {
        let resolved = self.resolve(ty);
        if self.methods_for_type(&resolved, method).is_some() {
            return true;
        }
        // UFCS: `recv.m(..)` falls back to a visible free function `m(recv, ..)`.
        if self.program.functions.contains_key(method) {
            return true;
        }
        match resolved {
            Type::Str => method == "len",
            Type::Slice(_) => matches!(method, "push" | "pop" | "insert" | "remove" | "len"),
            Type::Array(_, _) => method == "len",
            Type::Record(rec) if rec.is_name("File") => {
                matches!(method, "read" | "write" | "close" | "size" | "seek")
            }
            // A user record/sum, or a primitive, with no matching member above
            // genuinely lacks the method.
            Type::Record(_)
            | Type::Sum(_)
            | Type::Int(_)
            | Type::Float(_)
            | Type::Bool
            | Type::Void => false,
            _ => true,
        }
    }

    /// Whether a resolved concrete record type exposes a field. Conservative for
    /// non-record types in the same way as `concrete_type_has_method`.
    fn concrete_type_has_field(&self, ty: &Type, field: &str) -> bool {
        match self.resolve(ty) {
            Type::Record(rec) => {
                if rec.substitution.get(field).is_some() {
                    return true;
                }
                match self.program.type_by_id(rec.id) {
                    Some(info) => match &info.kind {
                        TypeKind::Record { fields, .. } => fields.iter().any(|f| f.name == field),
                        TypeKind::Sum { .. } => false,
                    },
                    None => true,
                }
            }
            Type::Int(_) | Type::Float(_) | Type::Bool | Type::Void | Type::Str => false,
            _ => true,
        }
    }

    pub(super) fn is_in_scope(&self, base: &Expr, scopes: &ScopeStack) -> bool {
        matches!(base, Expr::Ident(name, _) if self.lookup(scopes, name).is_some())
    }

    pub(super) fn resolve_self_name(&self, name: &str) -> String {
        if name == "Self" {
            self.self_type.clone().unwrap_or_default()
        } else {
            name.to_string()
        }
    }

    /// The unique storage symbol of a user type named `name`, resolved from the
    /// current module: own/unique, this module's qualified
    /// definition, or the imported one. Returns an owned String so the borrow
    /// does not outlive into later `&mut self` use.
    pub(super) fn resolve_type_symbol(&self, name: &str) -> Option<String> {
        self.program
            .resolve_type(&self.current_module, name)
            .map(|t| t.symbol.clone())
    }

    /// The `Type` of a user type named `name`, resolved from the current module.
    pub(super) fn resolve_type_ref(&self, name: &str) -> Option<Type> {
        self.program
            .resolve_type(&self.current_module, name)
            .map(|t| t.type_ref())
    }

    pub(super) fn is_type_word(&self, name: &str) -> bool {
        if name.contains('.') {
            return self
                .program
                .resolve_type(&self.current_module, name)
                .is_some();
        }
        // A renamed import (`import m.{ Vec2 as V }`): the local name appears
        // in no type table; resolve it through the rename-aware lookup.
        if self.import_remote(name).is_some() {
            return self
                .program
                .resolve_type(&self.current_module, name)
                .is_some();
        }
        self.program.has_type_named(name)
            || self.program.type_aliases.contains_key(name)
            || self
                .program
                .type_aliases
                .keys()
                .any(|k| k.starts_with(name) && k[name.len()..].starts_with('@'))
            || name == "Self"
            || name == "File"
            || IntKind::from_name(name).is_some()
            || matches!(name, "float32" | "float64" | "string" | "bool")
    }

    pub(super) fn is_unit_variant_name(&self, name: &str) -> bool {
        self.program.types.values().any(|info| match &info.kind {
            TypeKind::Sum { variants } => variants
                .iter()
                .any(|v| v.name == name && v.fields.is_empty()),
            TypeKind::Record { .. } => false,
        })
    }

    /// A sum type defining a variant named `variant`, when one exists. Several
    /// sums may share a variant name; the first of the deterministic order is
    /// returned (used for messages and as a fallback when the scrutinee's own
    /// type is unknown), so results never depend on type-table hash order.
    pub(super) fn variant_owner(&self, variant: &str) -> Option<String> {
        self.program
            .sums_containing_variant(variant)
            .first()
            .map(|info| info.name.clone())
    }
}
