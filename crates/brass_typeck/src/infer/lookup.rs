//! Name, method, and module-visibility lookup: resolving methods for a
//! receiver type, static call qualifiers, functions and imports across
//! module boundaries, and `Self`/type-symbol naming. Also owns the
//! shape constraints recorded on inference variables, verified here
//! against the capabilities the solved type actually exposes.

use super::*;

impl<'a> Checker<'a> {
    /// Reject calling a function binding by a language construct's name.
    /// Non-function bindings remain available as ordinary values.
    pub(super) fn check_construct_binding(
        &mut self,
        name: &str,
        span: brass_parser::Span,
        scopes: &ScopeStack,
    ) {
        if matches!(name, "error" | "typeof" | "fields" | "spawn" | "with")
            && let Some(ty) = self.lookup(scopes, name)
            && matches!(peel_modes(&self.resolve(&ty)), Type::Fun(..))
        {
            self.errors.push(TypeError {
                message: format!(
                    "`{name}(..)` means the language construct; rename the function binding `{name}` to call it"
                ),
                span,
            });
        }
    }

    /// The declarations a call of `method` on a value of type `ty` reaches: a
    /// record's own method (with the receiver instance's substitution
    /// applied), or one candidate per variant of a sum (keyed
    /// `Sum.Variant`), all of which must declare it. `None` for any other
    /// receiver or when the method is missing.
    pub(super) fn methods_for_type(&self, ty: &Type, method: &str) -> Option<Vec<ResolvedMethod>> {
        // Mode wrappers expose the underlying value's methods: a call through a
        // `ref(mut(T))` parameter resolves (and type-checks its arguments
        // against) `T`'s methods.
        match brass_hir::peel_modes(&self.resolve(ty)).clone() {
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
                    method: Rc::clone(&m.decl),
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
                            method: Rc::clone(&method.decl),
                        })
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(methods)
            }
            _ => None,
        }
    }

    /// The method a static call `qualifier.method(..)` names: a variant's
    /// method for a `Sum.Variant` qualifier, else the method of the record or
    /// sum the qualifier (a type name, `Self`, an alias or a storage symbol)
    /// resolves to from the current module.
    pub(super) fn method_for_qualifier(
        &self,
        qualifier: &str,
        method: &str,
    ) -> Option<ResolvedMethod> {
        // `Sum.Variant.method()`: only when the first segment is actually a
        // type (not a module alias producing a marker like `"vec.Vec2"`).
        if let Some((sum, variant)) = qualifier.rsplit_once('.')
            && let Some(info) = self
                .program
                .resolve_type_or_alias(&self.current_module, &self.resolve_self_name(sum))
                .or_else(|| {
                    sum.contains('@')
                        .then(|| self.program.types.get(sum))
                        .flatten()
                })
        {
            let symbol = &info.symbol;
            if let Some(v_method) = info.variant(variant).and_then(|v| v.methods.get(method)) {
                return Some(ResolvedMethod {
                    qualifier: format!("{}.{variant}", info.symbol),
                    self_type: symbol.clone(),
                    signature: v_method.signature.clone(),
                    method: Rc::clone(&v_method.decl),
                });
            }
        }
        let type_name = self.resolve_self_name(qualifier);
        // A type-ALIAS qualifier (`type Names = Stack { .. }`; `Names.new()`)
        // answers with its TARGET's declaration: the alias is not a nominal of
        // its own and declares no methods, so the lookup follows it.
        let info = self
            .program
            .resolve_type_or_alias(&self.current_module, &type_name)
            .or_else(|| {
                type_name
                    .contains('@')
                    .then(|| self.program.types.get(&type_name))
                    .flatten()
            })?;
        let symbol = info.symbol.clone();
        match &info.kind {
            TypeKind::Record { methods, .. } => {
                let method = methods.get(method)?;
                Some(ResolvedMethod {
                    qualifier: info.symbol.clone(),
                    self_type: symbol,
                    signature: method.signature.clone(),
                    method: Rc::clone(&method.decl),
                })
            }
            // A method declared on a SUM (`fun TomlValue.parse`) is lowered into
            // every variant's table, so the bare type name is answered by any
            // variant -- they hold the same declaration. This is the only way to
            // reach a sum's STATIC method: with no `self` there is no receiver to
            // dispatch through, so `methods_for_type` never runs. Keying the
            // resolution as `Sum.Variant` matches what the receiver path and
            // `precompute_returns` file sum methods under, so the call reads
            // the same `method_returns` entry.
            TypeKind::Sum { variants } => {
                let variant = variants.iter().find(|v| v.methods.contains_key(method))?;
                let m = variant.methods.get(method)?;
                Some(ResolvedMethod {
                    qualifier: format!("{}.{}", info.symbol, variant.name),
                    self_type: symbol,
                    signature: m.signature.clone(),
                    method: Rc::clone(&m.decl),
                })
            }
        }
    }

    /// Report a call that resolved to several variant methods (a sum
    /// receiver) whose signatures do not satisfy each other: one call must
    /// type the same way whichever variant the value is.
    pub(super) fn check_common_method_signatures(
        &mut self,
        methods: &[ResolvedMethod],
        method: &str,
        span: brass_parser::Span,
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

    /// The static-call qualifier of the receiver `expr` of a call to
    /// `method`, or `None` when the call is an instance call. This is
    /// [`Self::static_qualifier`] except for a UNIT variant naming an
    /// instance method (`L.Nil.size()`): the unit variant is a value of its
    /// sum, so the call dispatches on that value, exactly like
    /// `let n = L.Nil` followed by `n.size()`. A static method reached
    /// through a variant qualifier (`Token.Ident.make()`) stays static.
    pub(super) fn static_call_qualifier(
        &self,
        expr: &Expr,
        method: &str,
        scopes: &ScopeStack,
    ) -> Option<String> {
        let qualifier = self.static_qualifier(expr, scopes)?;
        if let Expr::Field(base, variant, _) = expr
            && matches!(&**base, Expr::Ident(..))
            && let Some((sum, _)) = qualifier.rsplit_once('.')
            && let Some(info) = self.program.types.get(sum)
            && info.variant(variant).is_some_and(|v| {
                v.fields.is_empty()
                    && v.methods.get(method).is_some_and(|m| {
                        m.signature.params.first().is_some_and(|p| p.name == "self")
                    })
            })
        {
            return None;
        }
        Some(qualifier)
    }

    /// The type a receiver expression names when it is a static-call
    /// qualifier rather than a value: a type word not shadowed by a local
    /// binding (`Self` resolved), `typeof(v)` of a binding whose type is
    /// known, or `Type.Variant` (as `<sum symbol>.<variant>`). `None` for a
    /// value receiver.
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
                self.type_qualifier(&ty)
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
                    .resolve_type_or_alias(&self.current_module, &resolved)
                    .or_else(|| {
                        resolved
                            .contains('@')
                            .then(|| self.program.types.get(&resolved))
                            .flatten()
                    })?;
                info.variant(variant)
                    .map(|_| format!("{}.{variant}", info.symbol))
            }
            _ => None,
        }
    }

    /// The type of a module-level global reached through a module QUALIFIER
    /// (`m.VERSION`, which the resolve pass rewrote to the dotted marker
    /// `m.VERSION`). The qualifier names no import of the global itself, so the
    /// scope does not hold it; it is read from its defining module directly.
    ///
    /// A renamed import needs nothing here: the scope already carries the global
    /// under the local name the rename gave it.
    pub(super) fn lookup_aliased_global(&self, name: &str) -> Option<Type> {
        let (alias, bare) = name.split_once('.')?;
        let origin = self
            .program
            .module_aliases
            .get(&self.current_module)?
            .get(alias)?;
        self.global_defs.get(origin)?.get(bare).cloned()
    }

    /// The static-call qualifier naming the type `ty` (the receiver a
    /// `typeof(v)` stands for): a declared record or sum's table symbol, a
    /// primitive's name. `None` while the type is still open.
    pub(super) fn type_qualifier(&self, ty: &Type) -> Option<String> {
        match brass_hir::peel_modes(&self.resolve(ty)) {
            Type::Record(n) | Type::Sum(n) => self
                .program
                .type_by_id(n.id)
                .map(|info| info.symbol.clone()),
            Type::Unknown(_) => None,
            other => Some(other.type_name()),
        }
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

    /// The function type of the free function `name` used as a value, when its
    /// signature fixes that type: every parameter is annotated with a fully
    /// known type, so the function is monomorphic. A function value is compiled
    /// once for exactly this signature, so a flow of it is checked against the
    /// signature rather than left open -- including the passing mode of each
    /// parameter (a `ref(mut(T))` parameter writes through). `None` for a
    /// generic (partly unannotated) function, whose type each call recovers,
    /// and for one with an implicit trailing `Location` (a call fills it, a
    /// value cannot).
    ///
    /// An omitted return is inferred from the body, and a `T!` return names
    /// only the Ok payload; the return table completes either (a caller
    /// forwarding the value's Result needs that error type). A return the
    /// table has not settled leaves the value open.
    pub(super) fn annotated_function_value_type(&self, name: &str) -> Option<Type> {
        let info = self.lookup_function(name)?;
        let signature = &info.signature;
        if signature
            .params
            .iter()
            .any(|p| p.ty.is_none() || param_is_location(self.program, p))
        {
            return None;
        }
        let params = signature
            .params
            .iter()
            .map(|p| p.resolved_ty.clone())
            .collect::<Option<Vec<_>>>()?;
        let ret = match &signature.ret_ty {
            Some(declared) if brass_hir::is_fully_known(declared) => declared.clone(),
            _ => self.resolve(self.function_returns.get(&info.symbol)?),
        };
        let fun = Type::Fun(params, Box::new(ret));
        brass_hir::is_fully_known(&fun).then_some(fun)
    }

    /// Whether a program free function `name` is visible from the module being
    /// checked: defined in that module, implicitly imported as
    /// part of the standard-library prelude, or brought in by an `import`.
    fn is_function_visible(&self, name: &str) -> bool {
        self.lookup_function(name).is_some()
    }

    /// Resolve a bare free-function name to its definition from the current
    /// module, by the program's one resolution rule
    /// ([`brass_hir::Program::resolve_function`], which MIR lowering and the
    /// back ends use too): this module's own definition first -- so a module
    /// declaring a prelude name such as `println` shadows the prelude there
    /// -- then the one brought in by an `import`, then a visible unique or
    /// prelude definition. A `_`-prefixed prelude helper is private to its
    /// module and never resolves from user code.
    pub(super) fn lookup_function(&self, name: &str) -> Option<&brass_hir::FunInfo> {
        let info = self.program.resolve_function(&self.current_module, name)?;
        let private_prelude = name.starts_with('_')
            && info.module != self.current_module
            && self.program.prelude_modules.contains(&info.module);
        (!private_prelude).then_some(info)
    }

    /// Whether a call of `name` is the implicit prelude's function of that
    /// name (or, in a program without the prelude, the runtime builtin the
    /// name denotes): no local binding and no user definition visible here
    /// shadows it. The checker types a few prelude calls (`print`,
    /// `println`, `assert`, `input`) directly instead of elaborating their
    /// bodies; that shortcut applies only when the call really reaches the
    /// prelude, exactly as MIR lowering resolves it.
    pub(super) fn calls_prelude_function(&self, name: &str, local: bool) -> bool {
        !local
            && self
                .lookup_function(name)
                .is_none_or(|info| self.program.prelude_modules.contains(&info.module))
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
        // Only the implicit-prelude modules are visible with no import; the
        // core-library modules (`core.collections`, ...) follow the same
        // import rule as user modules.
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
    /// inference variable. Used while checking a body that operates on an
    /// unknown-typed value (a closure parameter); the constraint is verified
    /// when the variable is solved at an application (see
    /// `crate::constraint`).
    pub(super) fn record_shape(&mut self, ty: &Type, constraint: ShapeConstraint) {
        if let Type::Unknown(id) = self.resolve_head(ty) {
            self.journal_elaboration_shape(Type::Unknown(id), constraint.clone());
            self.shape_constraints
                .entry(id)
                .or_default()
                .push(constraint);
        }
    }

    /// Record what a binary operator requires of an operand whose type is
    /// still unknown, next to a concrete `string` or number: string
    /// concatenation needs the same type; a numeric operator needs a type the
    /// shared operator rule accepts with the other operand -- yielding the
    /// `result` the body was typed with, when that is a concrete number. Each
    /// operand is its type and, for an integer literal, its value.
    pub(super) fn record_binary_shape(
        &mut self,
        op: BinOp,
        (left, left_literal): (&Type, Option<brass_typesys::NumericLiteral>),
        (right, right_literal): (&Type, Option<brass_typesys::NumericLiteral>),
        result: &Type,
    ) {
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
        let comparison = matches!(op, BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge);
        let result = self.resolve(result);
        // The operation was typed as yielding a concrete number, or the open
        // operand itself (next to an adapting literal): either way the
        // concrete operation must yield exactly that.
        let open_operand = [left, right]
            .into_iter()
            .find(|t| matches!(t, Type::Unknown(_)))
            .cloned();
        let pinned = !comparison
            && (matches!(result, Type::Int(_) | Type::Float(_))
                || open_operand.as_ref() == Some(&result));
        let constraint = |other: &Type, literal: Option<brass_typesys::NumericLiteral>| match other
        {
            Type::Str => Some(ShapeConstraint::Equals(Type::Str)),
            Type::Int(_) | Type::Float(_) => Some(ShapeConstraint::Operand {
                op,
                other: other.clone(),
                literal,
                result: pinned.then(|| result.clone()),
            }),
            _ => None,
        };
        match (left, right) {
            (Type::Unknown(_), other) => {
                if let Some(c) = constraint(other, right_literal) {
                    self.record_shape(left, c);
                }
            }
            (other, Type::Unknown(_)) => {
                if let Some(c) = constraint(other, left_literal) {
                    self.record_shape(right, c);
                }
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
        span: brass_parser::Span,
    ) {
        let Type::Unknown(id) = self.resolve_head(var) else {
            return;
        };
        if matches!(self.resolve_head(got), Type::Unknown(_)) {
            return;
        }
        let Some(constraints) = self.shape_constraints.get(&id).cloned() else {
            return;
        };
        let got = self.resolve(got);
        for constraint in constraints {
            match constraint {
                ShapeConstraint::Equals(expected) => {
                    if !self.can_unify(&got, &expected) {
                        let (got, expected) = brass_hir::mismatch_display(&got, &expected);
                        self.errors.push(TypeError {
                            message: format!("cannot use `{got}` where `{expected}` is required"),
                            span,
                        });
                    }
                }
                ShapeConstraint::Operand {
                    op,
                    other,
                    literal,
                    result,
                } => {
                    let operand = peel_value_wrappers(&got);
                    let typing = brass_typesys::numeric_binary(
                        op,
                        brass_typesys::NumericOperand::value(operand),
                        brass_typesys::NumericOperand::new(&other, literal),
                    );
                    // An operation typed by this very operand (next to an
                    // adapting literal) must yield the argument's own type.
                    let result = result.map(|r| match self.resolve(&r) {
                        Type::Unknown(v) if v == id => operand.clone(),
                        r => r,
                    });
                    let accepted = typing
                        .is_ok_and(|typing| result.as_ref().is_none_or(|r| *r == typing.result));
                    if !accepted {
                        // An operation pinned to its own operand's type names
                        // the other operand's type as the requirement.
                        let expected = result.filter(|r| *r != got).unwrap_or(other);
                        let (got, expected) = brass_hir::mismatch_display(&got, &expected);
                        self.errors.push(TypeError {
                            message: format!("cannot use `{got}` where `{expected}` is required"),
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

    /// Whether a resolved type exposes `method`, for a deferred `HasMethod`
    /// shape: a declared record method, a method every variant of a sum
    /// declares, or the builtin `len` / growable-array mutators. A type that
    /// is not concrete (an unsolved variable, a nullable, a function, ...)
    /// answers `true`, so only a concrete receiver is judged.
    fn concrete_type_has_method(&self, ty: &Type, method: &str) -> bool {
        let resolved = self.resolve(ty);
        let resolved = brass_hir::peel_modes(&resolved);
        if resolved.primitive_class().is_some_and(|class| {
            self.program
                .primitive_methods
                .contains_key(&(class.to_string(), method.to_string()))
        }) {
            return true;
        }
        let has_declared_method = match resolved {
            Type::Record(name) => self
                .program
                .type_by_id(name.id)
                .and_then(|info| match &info.kind {
                    TypeKind::Record { methods, .. } => Some(methods.contains_key(method)),
                    TypeKind::Sum { .. } => None,
                })
                .unwrap_or(false),
            Type::Sum(name) => self
                .program
                .type_by_id(name.id)
                .and_then(|info| match &info.kind {
                    TypeKind::Sum { variants } => Some(
                        !variants.is_empty()
                            && variants
                                .iter()
                                .all(|variant| variant.methods.contains_key(method)),
                    ),
                    TypeKind::Record { .. } => None,
                })
                .unwrap_or(false),
            _ => false,
        };
        if has_declared_method {
            return true;
        }
        match resolved {
            Type::Str => method == "len",
            Type::Slice(_) => matches!(method, "push" | "pop" | "insert" | "remove" | "len"),
            Type::Array(_, _) => method == "len",
            // A user record/sum, or a primitive, with no matching member above
            // genuinely lacks the method.
            Type::Record(_)
            | Type::Sum(_)
            | Type::Int(_)
            | Type::Float(_)
            | Type::Bool
            | Type::Fun(..)
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

    /// The storage symbol of the sum type a variant construction or unit
    /// variant names (`S.Variant`, `S.Variant { .. }`), resolved from the
    /// current module like [`Self::resolve_type_symbol`] and additionally
    /// through a `type A = S` alias. A sum alias is never a refinement, so
    /// the alias denotes exactly its target sum.
    pub(super) fn resolve_sum_head_symbol(&self, name: &str) -> Option<String> {
        self.program
            .resolve_type_or_alias(&self.current_module, name)
            .filter(|t| t.is_sum())
            .map(|t| t.symbol.clone())
    }

    /// The `Type` of a user type named `name`, resolved from the current module.
    pub(super) fn resolve_type_ref(&self, name: &str) -> Option<Type> {
        self.program
            .resolve_type(&self.current_module, name)
            .map(|t| t.type_ref())
    }

    /// Whether `name` names a type rather than a value: a declared type or
    /// alias (dotted, renamed on import, or bare), `Self`, or a primitive
    /// type word. Local bindings are not consulted: a caller rules out a
    /// shadowing local first.
    pub(super) fn is_type_word(&self, name: &str) -> bool {
        if name.contains('.') {
            return self
                .program
                .resolve_type_or_alias(&self.current_module, name)
                .is_some();
        }
        // A renamed import (`import m.{ Vec2 as V }`): the local name appears
        // in no type table; resolve it through the rename-aware lookup.
        if self.import_remote(name).is_some() {
            return self
                .program
                .resolve_type_or_alias(&self.current_module, name)
                .is_some();
        }
        self.program.has_type_named(name)
            || self.program.has_type_alias_named(name)
            || name == "Self"
            || IntKind::from_name(name).is_some()
            || matches!(name, "float32" | "float64" | "string" | "bool")
    }

    /// Whether an unqualified bare-name pattern `name` is a unit-variant test
    /// in the current module rather than a binding (the shared scoping rule,
    /// [`brass_hir::Program::is_unit_variant_in_scope`]).
    pub(super) fn is_unit_variant_name(&self, name: &str) -> bool {
        self.program
            .is_unit_variant_in_scope(&self.current_module, name)
    }

    /// A sum type defining a variant named `variant`, when one exists. Several
    /// sums may share a variant name; a sum in scope in the current module is
    /// preferred, then the first of the deterministic order is returned (used
    /// for messages and as a fallback when the scrutinee's own type is
    /// unknown), so results never depend on type-table hash order.
    pub(super) fn variant_owner(&self, variant: &str) -> Option<String> {
        self.program
            .pattern_scope(&self.current_module)
            .first_owner(variant, true)
            .map(|info| info.symbol.clone())
    }

    /// The owner of the variant an unqualified bare-name pattern `name`
    /// tests, when `name` is a variant of a sum in scope (unit or not); `None`
    /// when the name binds. Unlike [`Self::variant_owner`] an out-of-scope
    /// sum is never consulted, so a binding is never mistaken for one of its
    /// variants.
    pub(super) fn scoped_variant_owner(&self, name: &str) -> Option<String> {
        self.program
            .pattern_scope(&self.current_module)
            .first_owner(name, false)
            .map(|info| info.symbol.clone())
    }

    /// Whether the unqualified braced pattern head `name { .. }` destructures
    /// a matched value of type `scrutinee` as a sum variant rather than as a
    /// plain record (the shared rule,
    /// [`brass_hir::Program::braced_pattern_head`]): a head that is both a
    /// record type in scope and a variant is the record exactly when the
    /// value is that record; an open value is taken as the variant until its
    /// instance is known.
    pub(super) fn braced_head_is_variant(&self, name: &str, scrutinee: &Type) -> bool {
        match self.program.braced_pattern_head(&self.current_module, name) {
            brass_hir::BracedHead::Record => false,
            brass_hir::BracedHead::Variant => true,
            brass_hir::BracedHead::RecordOrVariant(record) => {
                let resolved = self.resolve_head(scrutinee);
                let value = match peel_modes(&resolved) {
                    Type::Nullable(inner) => peel_modes(inner).clone(),
                    other => other.clone(),
                };
                !matches!(value, Type::Record(n) if n.id == record.id)
            }
        }
    }
}
