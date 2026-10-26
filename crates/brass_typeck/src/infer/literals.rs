//! Typing of record and sum-variant literals and of field access.
//!
//! A literal's fields are checked against the declared (or refined) field
//! types, each literal instantiating the declaration's type slots afresh. A
//! record literal, a variant literal and a unit variant may name their type
//! through a type alias; a record literal through a refinement alias is built
//! as the record at the alias's instance. A field access is a unit variant
//! (`Sum.Variant`), a member-presence test, a record field (an absent one
//! reads as the always-null `never?`), or a sum field: on `self` in a method
//! checked for one variant, that variant's field, else the field every variant
//! declares alike.

use std::collections::BTreeMap;

use super::*;

/// What a record or variant literal is checked against: the literal's owner
/// (`who`, the record symbol or `Sum.Variant`), the variant (for payload
/// substitution keys), the declared fields, and the substitution of the
/// instance the literal is built as when something fixes it (a refinement
/// alias, or a requirement naming the same record).
pub(super) struct LiteralShape<'s> {
    pub(super) who: &'s str,
    pub(super) variant: Option<&'s str>,
    pub(super) declared: &'s [brass_hir::FieldInfo],
    pub(super) pins: Option<&'s Substitution>,
}

impl<'a> Checker<'a> {
    /// Check a record literal `name { fields }` (or an anonymous one when
    /// `name` is empty). `name` may be a `type A = R { .. }` alias of a record:
    /// the literal is then built as `R` at the alias's instance (its pinned
    /// fields and slots fix the literal's), exactly like an anonymous literal
    /// stored in a slot of type `A`. `pins` is the instance a requirement the
    /// literal flows into fixes, when it names the same record.
    pub(super) fn check_record_lit(
        &mut self,
        name: &str,
        fields: &[(String, Expr)],
        span: brass_parser::Span,
        pins: Option<&Substitution>,
        scopes: &mut ScopeStack,
    ) -> Type {
        // Anonymous structure literal `{ f: v, ... }`: a structural record whose
        // field types are the field value types.
        if name.is_empty() {
            let field_tys: Vec<(String, Type)> = fields
                .iter()
                .map(|(fname, e)| (fname.clone(), self.check_expr(e, scopes)))
                .collect();
            return brass_hir::structural_record(field_tys);
        }
        let tn = self.resolve_self_name(name);
        let (symbol, alias) = match self.resolve_type_symbol(&tn) {
            Some(symbol) => (symbol, None),
            None => match self.resolve_alias(&tn) {
                Some(Type::Record(n)) if n.id >= 0 => match self.program.type_by_id(n.id) {
                    Some(info) => (info.symbol.clone(), Some(n)),
                    None => {
                        self.check_supplied_field_exprs(fields, scopes);
                        return self.fresh_unknown();
                    }
                },
                _ => {
                    self.check_supplied_field_exprs(fields, scopes);
                    return self.fresh_unknown();
                }
            },
        };
        let Some(info) = self.program.types.get(&symbol) else {
            self.check_supplied_field_exprs(fields, scopes);
            return self.fresh_unknown();
        };
        let TypeKind::Record {
            fields: declared, ..
        } = &info.kind
        else {
            // A sum type constructed directly. `check_constructions` already
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
            self.check_supplied_field_exprs(fields, scopes);
            return self.fresh_unknown();
        };
        let Some(alias) = alias else {
            let ret = info.type_ref();
            let substitution = self.check_lit_fields(
                LiteralShape {
                    who: &symbol,
                    variant: None,
                    declared,
                    pins,
                },
                fields,
                span,
                scopes,
            );
            return apply_nominal_substitution(ret, substitution);
        };
        // Through an alias: the back ends know the record by its symbol.
        let declared = declared.clone();
        let substitution = self.check_lit_fields(
            LiteralShape {
                who: &symbol,
                variant: None,
                declared: &declared,
                pins: Some(&alias.substitution),
            },
            fields,
            span,
            scopes,
        );
        self.record_literal_nominal(span, symbol);
        overlay_nominal_substitution(Type::Record(alias), &substitution)
    }

    /// The nominal id of the record a construction head `name` names from the
    /// current module, directly or through a `type A = R { .. }` alias.
    pub(super) fn record_head_id(&self, name: &str) -> Option<i32> {
        self.program
            .resolve_type_or_alias(&self.current_module, &self.resolve_self_name(name))
            .filter(|info| !info.is_sum())
            .map(|info| info.id)
    }

    /// Check a variant literal `t.variant { fields }`, where `t` may name the
    /// sum through a `type A = S` alias (see `resolve_sum_head_symbol`). A
    /// missing variant is reported after module-aware head resolution.
    /// Recovery checks supplied field values and yields an open type.
    pub(super) fn check_variant_lit(
        &mut self,
        t: &str,
        variant: &str,
        fields: &[(String, Expr)],
        span: brass_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Type {
        let tn = self.resolve_self_name(t);
        let Some(symbol) = self.resolve_sum_head_symbol(&tn) else {
            self.check_supplied_field_exprs(fields, scopes);
            return self.fresh_unknown();
        };
        let Some(info) = self.program.types.get(&symbol) else {
            self.check_supplied_field_exprs(fields, scopes);
            return self.fresh_unknown();
        };
        let Some(var) = info.variant(variant) else {
            self.errors.push(TypeError {
                message: format!("`{t}` has no variant `{variant}`"),
                span,
            });
            self.check_supplied_field_exprs(fields, scopes);
            return self.fresh_unknown();
        };
        let ret = info.type_ref();
        let who = format!("{symbol}.{variant}");
        let substitution = self.check_lit_fields(
            LiteralShape {
                who: &who,
                variant: Some(variant),
                declared: &var.fields,
                pins: None,
            },
            fields,
            span,
            scopes,
        );
        apply_nominal_substitution(ret, substitution)
    }

    /// Recovery from an unresolved literal still evaluates every supplied field
    /// for typing purposes; otherwise the outer construction error would mask
    /// unrelated errors inside those expressions.
    fn check_supplied_field_exprs(&mut self, fields: &[(String, Expr)], scopes: &mut ScopeStack) {
        for (_, expr) in fields {
            self.check_expr(expr, scopes);
        }
    }

    /// Resolve a construction's field requirements using its refinement
    /// pins, fresh declaration slots, and the concrete meaning of `Self`.
    /// Wider structural literals reuse these requirements for matching fields.
    pub(super) fn literal_field_requirements(
        &mut self,
        shape: &LiteralShape<'_>,
    ) -> BTreeMap<String, Type> {
        let who = shape.who;
        let pins = shape.pins;
        // The concrete type `Self` denotes in a field type, so a closure-typed
        // field declared `(self, T) -> U` is checked with `self` bound to the
        // type being constructed rather than the abstract `Self`.
        let base_info = self.program.types.get(who.split('.').next().unwrap_or(who));
        let self_ty = base_info.map(|info| info.type_ref());
        // The declaration's type SLOTS are per-instance parameters. Each literal
        // instantiates them fresh -- one variable per slot for the WHOLE literal,
        // so two fields written over one slot stay linked within the instance --
        // rather than checking against the declaration's shared slot variables:
        // through those, the first literal's field values would pin every other
        // literal's slots program-wide (two `Stack { items: [...] }` of different
        // element types in one scope must not conflict).
        let slot_vars: Vec<(String, u32)> =
            base_info.map(|info| info.slots.clone()).unwrap_or_default();
        let slot_map: BTreeMap<u32, Type> = slot_vars
            .into_iter()
            .map(|(name, v)| {
                let pinned = pins.and_then(|p| p.get(&name)).cloned();
                (v, pinned.unwrap_or_else(|| self.fresh_unknown()))
            })
            .collect();
        shape
            .declared
            .iter()
            .filter_map(|field| {
                let declared = field.resolved_ty.as_ref()?;
                let want = match &self_ty {
                    Some(s) => substitute_self(declared, s),
                    None => declared.clone(),
                };
                let want = brass_hir::substitute_vars(&want, &slot_map);
                // A bare unannotated field is shared by the declaration's uses;
                // each construction instead gets its own unknown or pinned type.
                let pinned = pins
                    .filter(|_| !self.solver.free_vars(&want).is_empty())
                    .and_then(|p| p.get(&field_substitution_key(shape.variant, &field.name)))
                    .cloned();
                let want = match pinned {
                    Some(pin) => pin,
                    None if want.is_unknown() => self.fresh_unknown(),
                    None => want,
                };
                Some((field.name.clone(), want))
            })
            .collect()
    }

    /// Check a record or variant literal's `fields` against `shape`,
    /// returning the instance substitution its open fields take. An open
    /// field or slot the shape's `pins` fix (a refinement such as
    /// `Box { item: int64 }`) is checked against the pinned type, so a
    /// literal value adapts to it.
    pub(super) fn check_lit_fields(
        &mut self,
        shape: LiteralShape<'_>,
        fields: &[(String, Expr)],
        span: brass_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Substitution {
        let requirements = self.literal_field_requirements(&shape);
        let LiteralShape {
            who,
            variant,
            declared,
            pins: _,
        } = shape;
        let mut substitution = Substitution::empty();
        let mut seen = HashSet::default();
        for (name, expr) in fields {
            if !seen.insert(name) {
                self.errors.push(TypeError {
                    message: format!("`{who}` literal repeats field `{name}`"),
                    span: expr.span(),
                });
            }
        }
        for field in declared {
            match fields.iter().find(|(name, _)| name == &field.name) {
                Some((_, expr)) => {
                    // Judged on the declaration as written, not through the
                    // solver: checking (this literal's or an earlier one's)
                    // may bind the declaration's shared variable -- an
                    // `infer[]` field pinned by its value -- and every
                    // instance must still carry the type it gave the field.
                    let inferred_field = field
                        .resolved_ty
                        .as_ref()
                        .is_some_and(|t| !brass_hir::is_fully_known(t));
                    let got = if let Some(want) = requirements.get(&field.name) {
                        let want = want.clone();
                        // An array-literal value for a sequence-typed slot field
                        // whose element THIS literal must pin (still open after
                        // the per-literal instantiation): type it bottom-up (the
                        // elements decide, as for an unannotated field) and
                        // COMMIT the result to the instance's element variable.
                        // The element-wise against-check only probes, and an
                        // unpinned element would accept a conflicting later
                        // store on the same instance. Safe to commit here and
                        // only here: `want`'s open variables are this literal's
                        // own instantiation, never a shared signature type.
                        let resolved_want = self.resolve(&want);
                        let open_seq_elem = matches!(expr, Expr::Array(..))
                            && match &resolved_want {
                                Type::Slice(e) | Type::Array(e, _) => self.resolve(e).is_unknown(),
                                _ => false,
                            };
                        if open_seq_elem {
                            let got = self.check_expr(expr, scopes);
                            if self.solver.unify(&got, &want).is_err() {
                                self.expect_expr_assignable(&got, &want, expr);
                            }
                            got
                        } else {
                            self.check_expr_against(expr, &want, scopes)
                        }
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
    /// the enclosing sum type. `base` must name a sum type, possibly through a
    /// type alias, rather than a value in scope (`in_scope`). Returns `None`
    /// when this is an ordinary field access. Variants with fields are
    /// excluded: they require `{ ... }` construction, handled elsewhere.
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
        let info = self.program.types.get(&resolved).or_else(|| {
            self.program
                .resolve_type_or_alias(&self.current_module, &resolved)
        })?;
        let variant = info.variant(name)?;
        if variant.fields.is_empty() {
            Some(info.type_ref())
        } else {
            None
        }
    }

    /// Type the field access `base.name` (not called): a unit variant, a
    /// member-presence test, or a field read, as the module doc lists. A
    /// nullable base is reported; an open one records that it must have the
    /// field (see `ShapeConstraint::HasField`).
    pub(super) fn check_field(
        &mut self,
        base: &Expr,
        name: &str,
        span: brass_parser::Span,
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
            if let Some(info) = self.program.types.get(&resolved).or_else(|| {
                self.program
                    .resolve_type_or_alias(&self.current_module, &resolved)
            }) && info.is_sum()
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
        let peeled = brass_hir::peel_modes(&resolved).clone();
        // An uncalled member access is a compile-time presence test wherever the
        // name can only be a method: on a `string`/array/scalar receiver (no
        // fields at all), and on a record/sum whose declaration carries a method
        // of that name. A present method decays to its own NAME as a string
        // (exactly as a `fields()` descriptor does); a member a primitive class
        // does not have is the always-null `never?`; anything else falls through
        // to ordinary field lookup. A generic body branches on this to pick the
        // arm that fits its instantiation.
        if let Some(present) = self.program.member_presence(&peeled, name) {
            return if present { Type::Str } else { Type::null() };
        }
        match peeled {
            Type::Record(record) => {
                if let Some(ty) = record.substitution.get(name) {
                    return ty.clone();
                }
                if let Some(info) = self.program.type_by_id(record.id)
                    && let TypeKind::Record { fields, .. } = &info.kind
                    && let Some(field) = fields.iter().find(|f| f.name == name)
                {
                    // A field declared with `Self` (`next: Self?`) names its
                    // own record type, as at construction.
                    return match &field.resolved_ty {
                        Some(ty) => brass_hir::substitute_self(ty, &info.type_ref()),
                        None => self.fresh_unknown(),
                    };
                }
                // A field the record does not have reads as the always-null
                // `never?` (the member-presence rule): an `if` on it is
                // statically false (then-branch pruned), and using it as a
                // non-null value is still rejected, which keeps structural
                // checks sound.
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

    /// While a sum method's body is checked for one variant (its
    /// `Sum.Variant` qualifier, `Checker::self_variant`), `self.name` reads
    /// that variant's field. `None` when `base` is not such a `self`.
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
        if self.program.types.get(&self_sum).map(|info| info.id) != Some(sum.id) {
            return None;
        }
        self.variant_field_type(sum, &variant, name)
    }

    fn variant_field_type(&mut self, sum: &NominalType, variant: &str, name: &str) -> Option<Type> {
        let fallback = self
            .program
            .type_by_id(sum.id)?
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

    /// The type of the field `name` read from a value of the sum `sum` whose
    /// variant is not known: every variant must declare it, at types that
    /// unify. `None` when one does not, when the types conflict, or when the
    /// read is unsound for a bare sum value (see below).
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
