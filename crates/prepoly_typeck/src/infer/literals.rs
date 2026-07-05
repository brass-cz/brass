//! Typing of record and sum-variant literals and of field access:
//! literal field lists checked against declared (or refined) field
//! types, unit-variant names, and the per-variant/common field type of
//! a sum scrutinee.

use super::*;

impl<'a> Checker<'a> {
    pub(super) fn check_record_lit(
        &mut self,
        name: &str,
        fields: &[(String, Expr)],
        span: prepoly_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        // Anonymous structure literal `{ f: v, ... }`: a structural record whose
        // field types are the field value types.
        if name.is_empty() {
            let field_tys: Vec<(String, Type)> = fields
                .iter()
                .map(|(fname, e)| (fname.clone(), self.check_expr(e, scopes)))
                .collect();
            return prepoly_hir::structural_record(field_tys);
        }
        let tn = self.resolve_self_name(name);
        let Some(symbol) = self.resolve_type_symbol(&tn) else {
            return self.fresh_unknown();
        };
        let Some(info) = self.program.types.get(&symbol) else {
            return self.fresh_unknown();
        };
        let TypeKind::Record {
            fields: declared, ..
        } = &info.kind
        else {
            // A sum type constructed directly. check_constructions already
            // reports the direct-table (bare unique) spelling; report the
            // forms only module-aware resolution can name -- a qualified
            // marker (`alias.Sum`), a renamed local, a multi-module import --
            // so the mistake does not surface as a span-less back-end error.
            if !self.program.types.contains_key(&tn) {
                self.errors.push(TypeError {
                    message: format!(
                        "`{tn}` is a sum type; construct a variant with `{tn}.Variant {{ ... }}`"
                    ),
                    span,
                });
            }
            return self.fresh_unknown();
        };
        let ret = info.type_ref();
        let substitution = self.check_lit_fields(&symbol, None, declared, fields, span, scopes);
        apply_nominal_substitution(ret, substitution)
    }

    pub(super) fn check_variant_lit(
        &mut self,
        t: &str,
        variant: &str,
        fields: &[(String, Expr)],
        span: prepoly_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        let tn = self.resolve_self_name(t);
        let Some(symbol) = self.resolve_type_symbol(&tn) else {
            return self.fresh_unknown();
        };
        let Some(info) = self.program.types.get(&symbol) else {
            return self.fresh_unknown();
        };
        let Some(var) = info.variant(variant) else {
            return self.fresh_unknown();
        };
        let ret = info.type_ref();
        let substitution = self.check_lit_fields(
            &format!("{symbol}.{variant}"),
            Some(variant),
            &var.fields,
            fields,
            span,
            scopes,
        );
        apply_nominal_substitution(ret, substitution)
    }

    fn check_lit_fields(
        &mut self,
        who: &str,
        variant: Option<&str>,
        declared: &[prepoly_hir::FieldInfo],
        fields: &[(String, Expr)],
        span: prepoly_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Substitution {
        let mut substitution = Substitution::empty();
        let mut seen = HashSet::new();
        for (name, expr) in fields {
            if !seen.insert(name) {
                self.errors.push(TypeError {
                    message: format!("`{who}` literal repeats field `{name}`"),
                    span: expr.span(),
                });
            }
        }
        // The concrete type `Self` denotes in a field type, so a closure-typed
        // field declared `(self, T) -> U` is checked with `self` bound to the
        // type being constructed rather than the abstract `Self`.
        let self_ty = self
            .program
            .types
            .get(who.split('.').next().unwrap_or(who))
            .map(|info| info.type_ref());
        for field in declared {
            match fields.iter().find(|(name, _)| name == &field.name) {
                Some((_, expr)) => {
                    let got = if let Some(want) = &field.resolved_ty {
                        let want = match &self_ty {
                            Some(s) => substitute_self(want, s),
                            None => want.clone(),
                        };
                        // A bare unannotated field's declared variable is SHARED
                        // by every use of the declaration -- method co-checking
                        // deliberately binds through it (the scheme links the
                        // type and its methods). A literal must not check its
                        // value against whatever that co-checking bound (the
                        // binding mixes another body's local variables in), so
                        // each literal checks against a fresh variable and
                        // records the value's own type in the substitution
                        // below. Partially-inferred annotations (an `infer?[]`
                        // slot) keep the shared variable: the store-pin
                        // machinery relies on it.
                        let want = if want.is_unknown() {
                            self.fresh_unknown()
                        } else {
                            want
                        };
                        self.check_expr_against(expr, &want, scopes)
                    } else {
                        self.check_expr(expr, scopes)
                    };
                    // Record the field's value type in the instance substitution
                    // when the field's declared type still carries an inference
                    // variable: a bare unannotated field (`Unknown`), or a
                    // partially-inferred annotation like `infer?[]` (a slot array
                    // whose element is inferred from use). This carries the
                    // instance's resolved field type into the typed program and the
                    // back-end seed; a fully concrete annotation is static.
                    let inferred_field = field
                        .resolved_ty
                        .as_ref()
                        .is_some_and(|t| !self.solver.free_vars(t).is_empty());
                    if inferred_field {
                        substitution.insert(field_substitution_key(variant, &field.name), got);
                    }
                }
                None => self.errors.push(TypeError {
                    message: format!("`{who}` literal is missing field `{}`", field.name),
                    span,
                }),
            }
        }
        for (name, expr) in fields {
            if !declared.iter().any(|f| f.name == *name) {
                self.errors.push(TypeError {
                    message: format!("`{who}` has no field `{name}`"),
                    span: expr.span(),
                });
                self.check_expr(expr, scopes);
            }
        }
        substitution
    }

    /// A fieldless variant written without braces (`Sum.Variant`) is a value of
    /// the enclosing sum type. `base` must name a sum type
    /// rather than a value in scope. Returns `None` when this is an ordinary
    /// field access. Variants with fields are excluded: they require `{ ... }`
    /// construction, handled elsewhere.
    pub(super) fn unit_variant_type(
        &self,
        base: &Expr,
        name: &str,
        in_scope: bool,
    ) -> Option<Type> {
        let Expr::Ident(type_name, _) = base else {
            return None;
        };
        if in_scope {
            return None;
        }
        let resolved = self.resolve_self_name(type_name);
        let info = self
            .program
            .types
            .get(&resolved)
            .or_else(|| self.program.resolve_type(&self.current_module, &resolved))?;
        let variant = info.variant(name)?;
        if variant.fields.is_empty() {
            Some(info.type_ref())
        } else {
            None
        }
    }

    pub(super) fn check_field(
        &mut self,
        base: &Expr,
        name: &str,
        span: prepoly_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        if let Some(ty) = self.unit_variant_type(base, name, self.is_in_scope(base, scopes)) {
            return ty;
        }
        // `Sum.X` in value position is only valid for a fieldless variant
        // (handled above). Anything else is either a missing variant or a
        // variant that requires `{ ... }` construction.
        if let Expr::Ident(tname, _) = base
            && !self.is_in_scope(base, scopes)
        {
            let resolved = self.resolve_self_name(tname);
            if let Some(info) = self
                .program
                .types
                .get(&resolved)
                .or_else(|| self.program.resolve_type(&self.current_module, &resolved))
                && info.is_sum()
            {
                let message = match info.variant(name) {
                    Some(_) => format!(
                        "variant `{resolved}.{name}` has fields; construct it with `{resolved}.{name} {{ ... }}`"
                    ),
                    None => format!("`{resolved}` has no variant `{name}`"),
                };
                self.errors.push(TypeError { message, span });
                return self.fresh_unknown();
            }
        }
        let base_ty = self.check_expr(base, scopes);
        // A `ref`/`mut`/`const` view exposes the underlying value's members, so
        // the lookup peels the mode wrappers; otherwise a `ref(mut(T))` base
        // would fall to the permissive arm and skip field type checking.
        let resolved = self.resolve(&base_ty);
        match prepoly_hir::peel_modes(&resolved).clone() {
            Type::Record(record) => {
                if let Some(ty) = record.substitution.get(name) {
                    return ty.clone();
                }
                if let Some(info) = self.program.type_by_id(record.id)
                    && let TypeKind::Record { fields, methods } = &info.kind
                {
                    if let Some(field) = fields.iter().find(|f| f.name == name) {
                        return field
                            .resolved_ty
                            .clone()
                            .unwrap_or_else(|| self.fresh_unknown());
                    }
                    // A bare `recv.method` (method as a value) is left to the runtime.
                    if methods.contains_key(name) {
                        return self.fresh_unknown();
                    }
                }
                // Accessing a field a structure does not have is an inference
                // failure typed as the always-null `never?`: an `if` on it is
                // statically false (then-branch pruned), and using it as a non-null
                // value is still rejected, which keeps structural checks sound.
                Type::null()
            }
            Type::Sum(sum) => {
                if let Some(variant_ty) = self.self_variant_field_type(base, &sum, name) {
                    return variant_ty;
                }
                if let Some(common_ty) = self.common_sum_field_type(&sum, name) {
                    common_ty
                } else {
                    self.errors.push(TypeError {
                        message: format!("`{sum}` has no common field `{name}`"),
                        span,
                    });
                    self.fresh_unknown()
                }
            }
            Type::Nullable(_) => {
                self.report_nullable_use(span);
                self.fresh_unknown()
            }
            // A primitive has no fields; accessing one is a static error rather
            // than a deferred runtime shape. Method calls are
            // handled separately in `check_call`.
            other if is_concrete_primitive(&other) => {
                self.errors.push(TypeError {
                    message: format!("`{}` has no field `{name}`", other.display()),
                    span,
                });
                self.fresh_unknown()
            }
            // An unknown receiver defers: record that it must expose this field
            // so a closure like `(x) -> x.name` rejects a record without `name`
            // at its call site.
            Type::Unknown(_) => {
                self.record_shape(&base_ty, ShapeConstraint::HasField(name.to_string()));
                self.fresh_unknown()
            }
            _ => self.fresh_unknown(),
        }
    }

    pub(super) fn self_variant_field_type(
        &mut self,
        base: &Expr,
        sum: &NominalType,
        name: &str,
    ) -> Option<Type> {
        if !is_self_expr(base) {
            return None;
        }
        let (self_sum, variant) = self.self_variant.clone()?;
        if self_sum != sum.name() {
            return None;
        }
        self.variant_field_type(sum, &variant, name)
    }

    fn variant_field_type(&mut self, sum: &NominalType, variant: &str, name: &str) -> Option<Type> {
        let fallback = self
            .program
            .types
            .get(sum.name())?
            .variant(variant)?
            .fields
            .iter()
            .find(|field| field.name == name)
            .map(|field| field.resolved_ty.clone());
        let key = field_substitution_key(Some(variant), name);
        Some(
            sum.substitution
                .get(&key)
                .cloned()
                .or_else(|| fallback.flatten())
                .unwrap_or_else(|| self.fresh_unknown()),
        )
    }

    pub(super) fn common_sum_field_type(&mut self, sum: &NominalType, name: &str) -> Option<Type> {
        let field_types = match &self.program.type_by_id(sum.id)?.kind {
            TypeKind::Sum { variants } => variants
                .iter()
                .map(|variant| {
                    let field = variant.fields.iter().find(|field| field.name == name)?;
                    Some((
                        field_substitution_key(Some(&variant.name), name),
                        field.resolved_ty.clone(),
                    ))
                })
                .collect::<Option<Vec<_>>>()?,
            TypeKind::Record { .. } => return None,
        };
        let mut types = Vec::with_capacity(field_types.len());
        for (key, ty) in field_types {
            types.push(
                sum.substitution
                    .get(&key)
                    .cloned()
                    .or(ty)
                    .unwrap_or_else(|| self.fresh_unknown()),
            );
        }
        // On a bare sum value (no per-value refinement -- e.g. a parameter, or a
        // value widened from a refined one) every variant is possible, so an
        // unannotated (dynamic) field in any variant means the value of that variant
        // carries an arbitrary-typed field: reject common access (read it by matching
        // the variant). A refined value's substitution pins the constructed variant,
        // so its dynamic sibling variants do not make the access unsound -- this is
        // what keeps widening a refined sum to its bare nominal sound.
        if sum.substitution.is_empty() && types.iter().any(|ty| self.resolve(ty).is_unknown()) {
            return None;
        }
        let candidate = types
            .iter()
            .find(|ty| !self.resolve(ty).is_unknown())
            .or_else(|| types.first())?;
        types
            .iter()
            .all(|ty| self.can_unify(candidate, ty))
            .then(|| candidate.clone())
    }
}
