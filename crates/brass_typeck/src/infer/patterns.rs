//! Pattern typing: binding `match`, `if let`, `let` and `for` patterns against
//! a scrutinee type, validating their shapes, coverage and refutability, and
//! the nullable-use diagnostic (null narrowing itself lives in `narrowing`).
//!
//! A record or variant pattern on a nullable subject tests the present value
//! (see `pattern_subject`): it is refutable, and `null` takes the `else` or
//! `_` arm. A written qualifier (`Alias.Variant { .. }`) resolves through a
//! type alias like any type name.

use super::*;
use brass_hir::PatternTypeHead;

impl<'a> Checker<'a> {
    /// Report a nullable value used where a non-null one is required. When the
    /// use is (or contains) a read of a field an enclosing condition tested,
    /// say why the test did not help: only bindings narrow (a field can be
    /// reassigned through any alias of its record), so the field must be
    /// bound first.
    pub(super) fn report_nullable_use(&mut self, span: brass_parser::Span) {
        let tested = self
            .tested_field_reads
            .iter()
            .filter(|(read, _)| span.lo <= read.lo && read.hi <= span.hi)
            .min_by_key(|(read, _)| (read.lo, read.hi))
            .map(|(_, path)| path);
        let message = match tested {
            Some(path) => {
                let name = path.rsplit('.').next().unwrap_or(path);
                format!(
                    "nullable value must be checked for null before use: a field is not \
                     narrowed by testing it; bind it first: `if let {name} = {path} {{ ... }}`"
                )
            }
            None => "nullable value must be checked for null before use".to_string(),
        };
        self.errors.push(TypeError { message, span });
    }

    /// Bind the names `pat` introduces in the innermost frame of `scopes`,
    /// each at the type of its position in `ty`. A qualified name or a unit
    /// variant tests rather than binds.
    pub(super) fn bind_pattern(&mut self, pat: &Pattern, ty: &Type, scopes: &mut ScopeStack) {
        match pat {
            Pattern::Binding(name, qualifier, span) => {
                if qualifier.is_none() && !self.is_unit_variant_name(name) {
                    scopes.last_mut().unwrap().insert(name.clone(), ty.clone());
                    self.record_binding(name, *span, ty);
                }
            }
            Pattern::Record(variant, qualifier, fields, _) => {
                let ty = self.pattern_scrutinee_type(ty, variant, qualifier.as_ref());
                let field_types = self.pattern_field_types(&ty, variant);
                for fp in fields {
                    let fty = field_types
                        .get(&fp.name)
                        .cloned()
                        .unwrap_or_else(|| self.fresh_unknown());
                    if let Some(subpat) = &fp.pat {
                        self.bind_pattern(subpat, &fty, scopes);
                    } else {
                        self.record_binding(&fp.name, fp.span, &fty);
                        scopes.last_mut().unwrap().insert(fp.name.clone(), fty);
                    }
                }
            }
            Pattern::Array(pats, _) => match self.resolve(ty) {
                // Tuple destructuring binds each position to its element type.
                Type::Tuple(elems) => {
                    for (p, ety) in pats.iter().zip(elems) {
                        self.bind_pattern(p, &ety, scopes);
                    }
                }
                // An array: every position is the element type.
                Type::Array(inner, _) | Type::Slice(inner) => {
                    for p in pats {
                        self.bind_pattern(p, &inner, scopes);
                    }
                }
                // The subject's shape is not known here. Each position gets its OWN
                // variable rather than sharing one: the positions of a destructuring
                // are independent values, and coupling them would make `[k, v]` claim
                // `k` and `v` are the same type -- whichever the body constrained
                // first would then reject the other.
                _ => {
                    for p in pats {
                        let elem = self.fresh_unknown();
                        self.bind_pattern(p, &elem, scopes);
                    }
                }
            },
            Pattern::Wildcard(_) | Pattern::Literal(_, _) => {}
        }
    }

    /// Whether the resolved scrutinee type can produce a value matching a
    /// variant pattern named `variant`. Membership is decided against the
    /// scrutinee's OWN sum definition -- two sums may share a variant name, so
    /// picking an arbitrary "owning" sum from the type table and comparing its
    /// name would accept or reject depending on hash order. Declared sum
    /// subtyping does not import a parent's variants: a child has its own
    /// nominal variants. A value coerced to its parent is matched against the
    /// parent's definition. A written qualifier must therefore have the same
    /// nominal ID as the resolved scrutinee, even for related sums.
    fn scrutinee_accepts_variant(&mut self, scrutinee: &Type, variant: &str) -> bool {
        let resolved = self.pattern_subject(scrutinee);
        if resolved.is_result_type() {
            return matches!(variant, "Ok" | "Err");
        }
        match resolved {
            Type::Sum(sum) => match self.program.type_by_id(sum.id) {
                Some(info) => info.variant(variant).is_some(),
                // A synthesized sum must still share its owner's nominal identity.
                None => self.program.variant_owner_ids(variant).contains(&sum.id),
            },
            Type::Unknown(_) => true,
            _ => false,
        }
    }

    /// The value a refutable pattern tests: the scrutinee with its mode
    /// wrappers and one nullable layer peeled. A record or variant pattern on
    /// a nullable subject (`if let A { x } = f()` with `f -> S?`) tests the
    /// present value; `null` matches no such pattern and takes the `else` or
    /// `_` arm.
    fn pattern_subject(&self, scrutinee: &Type) -> Type {
        let resolved = self.resolve_head(scrutinee);
        match peel_modes(&resolved) {
            Type::Nullable(inner) => peel_modes(&self.resolve_head(inner)).clone(),
            other => other.clone(),
        }
    }

    /// Validate the pattern's shape and the uniqueness of all names it binds.
    pub(super) fn check_pattern_against(&mut self, scrutinee: &Type, pat: &Pattern) {
        self.check_pattern_bindings(pat, &mut HashSet::default());
        self.check_pattern_shape(scrutinee, pat);
    }

    /// Report a name `pat` binds more than once: a pattern, nested fields
    /// included, is one binding scope.
    pub(super) fn check_pattern_bindings(&mut self, pat: &Pattern, names: &mut HashSet<String>) {
        match pat {
            Pattern::Binding(name, None, span) if !self.is_unit_variant_name(name) => {
                self.check_pattern_binding(name, *span, names);
            }
            Pattern::Record(_, _, fields, _) => {
                for field in fields {
                    if let Some(pat) = &field.pat {
                        self.check_pattern_bindings(pat, names);
                    } else {
                        self.check_pattern_binding(&field.name, field.span, names);
                    }
                }
            }
            Pattern::Array(patterns, _) => {
                for pat in patterns {
                    self.check_pattern_bindings(pat, names);
                }
            }
            _ => {}
        }
    }

    fn check_pattern_binding(&mut self, name: &str, span: Span, names: &mut HashSet<String>) {
        if !names.insert(name.to_string()) {
            self.errors.push(TypeError {
                message: format!("`{name}` is bound more than once in this pattern"),
                span,
            });
        }
    }

    fn check_pattern_shape(&mut self, scrutinee: &Type, pat: &Pattern) {
        if let Pattern::Record(name, None, _, span) = pat
            && name.contains('.')
            && !self.check_record_pattern_type(scrutinee, name, *span)
        {
            return;
        }
        if let Pattern::Binding(name, Some(q), _) | Pattern::Record(name, Some(q), _, _) = pat
            && !self.check_pattern_qualifier(scrutinee, name, q, pat)
        {
            return;
        }
        match pat {
            Pattern::Binding(name, qualifier, span) => {
                // An unqualified name is a variant only when a sum in scope
                // declares it; otherwise it binds and has no owner to check.
                let owner = if qualifier.is_some() {
                    self.variant_owner(name)
                } else {
                    self.scoped_variant_owner(name)
                };
                if let Some(owner) = owner
                    && !self.scrutinee_accepts_variant(scrutinee, name)
                {
                    let other = self.resolve(scrutinee);
                    self.errors.push(TypeError {
                        message: format!(
                            "pattern variant `{name}` belongs to `{owner}`, not `{}`",
                            other.display()
                        ),
                        span: *span,
                    });
                }
            }
            Pattern::Record(name, qualifier, fields, span) => {
                let owner = if qualifier.is_some() || self.braced_head_is_variant(name, scrutinee) {
                    self.variant_owner(name)
                } else {
                    None
                };
                if let Some(owner) = &owner
                    && !self.scrutinee_accepts_variant(scrutinee, name)
                {
                    let other = self.resolve(scrutinee);
                    self.errors.push(TypeError {
                        message: format!(
                            "pattern variant `{name}` belongs to `{owner}`, not `{}`",
                            other.display()
                        ),
                        span: *span,
                    });
                }
                let field_types = self.pattern_field_types(scrutinee, name);
                for fp in fields {
                    let Some(field_ty) = field_types.get(&fp.name) else {
                        if owner.is_some() || name.contains('.') {
                            self.errors.push(TypeError {
                                message: format!("pattern `{name}` has no field `{}`", fp.name),
                                span: fp.span,
                            });
                        }
                        continue;
                    };
                    if let Some(subpat) = &fp.pat {
                        self.check_pattern_shape(field_ty, subpat);
                    }
                }
            }
            Pattern::Array(pats, _) => {
                // A tuple pattern checks each position against its element type and
                // must have exactly the tuple's arity.
                if let Type::Tuple(elems) = self.resolve(scrutinee) {
                    if pats.len() != elems.len() {
                        self.errors.push(TypeError {
                            message: format!(
                                "tuple pattern has length {}, but the tuple has {} elements",
                                pats.len(),
                                elems.len()
                            ),
                            span: pat.span(),
                        });
                    }
                    for (pat, ety) in pats.iter().zip(&elems) {
                        self.check_pattern_shape(ety, pat);
                    }
                    return;
                }
                let elem = match self.resolve(scrutinee) {
                    Type::Array(inner, len) => {
                        if pats.len() != len {
                            self.errors.push(TypeError {
                                message: format!(
                                    "array pattern has length {}, but scrutinee has length {}",
                                    pats.len(),
                                    len
                                ),
                                span: pat.span(),
                            });
                        }
                        *inner
                    }
                    Type::Slice(inner) => *inner,
                    _ => self.fresh_unknown(),
                };
                pats.iter()
                    .for_each(|pat| self.check_pattern_shape(&elem, pat));
            }
            Pattern::Literal(expr, span) => {
                let Some(lit_ty) = literal_pattern_type(expr) else {
                    return;
                };
                let scrutinee = self.resolve(scrutinee);
                if literal_pattern_matches(expr, &lit_ty, &scrutinee) {
                    return;
                }
                self.errors.push(TypeError {
                    message: format!(
                        "literal pattern of type `{}` cannot match `{}`",
                        lit_ty.display(),
                        scrutinee.display()
                    ),
                    span: *span,
                });
            }
            Pattern::Wildcard(_) => {}
        }
    }

    /// Reject a bare name in a refutable pattern position (a `match` arm or
    /// `if let`) that binds a new variable although the matched value's own
    /// sum declares a unit variant of that name: the sum is not in scope here,
    /// so the name is no variant test, and silently binding would turn the
    /// arm into a catch-all.
    pub(super) fn check_out_of_scope_variant_binding(&mut self, scrutinee: &Type, pat: &Pattern) {
        let Pattern::Binding(name, None, span) = pat else {
            return;
        };
        if self.is_unit_variant_name(name) {
            return;
        }
        let Type::Sum(sum) = self.pattern_subject(scrutinee) else {
            return;
        };
        let Some(info) = self.program.type_by_id(sum.id) else {
            return;
        };
        if info.variant(name).is_some_and(|v| v.fields.is_empty()) {
            self.errors.push(TypeError {
                message: format!(
                    "`{name}` binds a new name, but the matched `{}` has a variant `{name}` \
                     that is not in scope here; import `{}` to match the variant, or rename the binding",
                    info.name, info.name
                ),
                span: *span,
            });
        }
    }

    /// Resolve a pattern's written type through module imports and aliases.
    /// Light inference uses this without emitting diagnostics; the full pass
    /// validates the variant and its agreement with the scrutinee separately.
    pub(super) fn pattern_qualifier_type(&self, q: &PatternQualifier) -> Option<Type> {
        let name = self.resolve_self_name(&q.ty);
        match self
            .program
            .pattern_scope(&self.current_module)
            .type_head(&name)
        {
            PatternTypeHead::Nominal(info) => Some(info.type_ref()),
            _ => None,
        }
    }

    /// An open scrutinee takes its field types from the written nominal head:
    /// a sum qualifier or a complete module-qualified record type marker.
    pub(super) fn pattern_scrutinee_type(
        &self,
        scrutinee: &Type,
        name: &str,
        qualifier: Option<&PatternQualifier>,
    ) -> Type {
        let resolved = self.resolve(scrutinee);
        if resolved.is_unknown()
            && let Some(q) = qualifier
        {
            return self.pattern_qualifier_type(q).unwrap_or(resolved);
        }
        if resolved.is_unknown() && name.contains('.') {
            return self
                .program
                .record_pattern_head(&self.current_module, name)
                .map(|info| info.type_ref())
                .unwrap_or(resolved);
        }
        resolved
    }

    /// A dotted record head is the complete type marker produced by qualified
    /// name resolution, rather than a sum qualifier plus a variant name.
    fn check_record_pattern_type(
        &mut self,
        scrutinee: &Type,
        name: &str,
        span: brass_parser::Span,
    ) -> bool {
        let PatternTypeHead::Nominal(info) = self
            .program
            .pattern_scope(&self.current_module)
            .type_head(name)
        else {
            self.errors.push(TypeError {
                message: format!("unknown type `{name}`"),
                span,
            });
            return false;
        };
        if info.is_sum() {
            self.errors.push(TypeError {
                message: format!(
                    "`{name}` is a sum type; match a variant with `{name}.Variant {{ ... }}`"
                ),
                span,
            });
            return false;
        }
        self.check_pattern_type_agreement(scrutinee, &info.type_ref(), name, name, span)
    }

    fn check_pattern_qualifier(
        &mut self,
        scrutinee: &Type,
        variant: &str,
        q: &PatternQualifier,
        pat: &Pattern,
    ) -> bool {
        let name = self.resolve_self_name(&q.ty);
        let head = self
            .program
            .pattern_scope(&self.current_module)
            .type_head(&name);
        let PatternTypeHead::Nominal(info) = head else {
            let known_alias = matches!(head, PatternTypeHead::NonNominalAlias);
            self.errors.push(TypeError {
                message: if known_alias
                    || IntKind::from_name(&name).is_some()
                    || matches!(name.as_str(), "bool" | "string" | "float32" | "float64")
                {
                    format!("`{}` has no variant `{variant}`", q.ty)
                } else {
                    format!("unknown type `{}`", q.ty)
                },
                span: q.span,
            });
            return false;
        };
        let Some(declared) = info.variant(variant) else {
            self.errors.push(TypeError {
                message: format!("`{}` has no variant `{variant}`", q.ty),
                span: pat.span(),
            });
            return false;
        };
        if matches!(pat, Pattern::Binding(..)) && !declared.fields.is_empty() {
            self.errors.push(TypeError {
                message: format!(
                    "variant `{}.{variant}` has fields; match it with `{}.{variant} {{ ... }}`",
                    q.ty, q.ty
                ),
                span: pat.span(),
            });
            return false;
        }
        self.check_pattern_type_agreement(
            scrutinee,
            &info.type_ref(),
            &format!("{}.{variant}", q.ty),
            &q.ty,
            q.span,
        )
    }

    /// A written nominal pattern must select the declaration of the scrutinee
    /// (of its present value, when nullable). An open scrutinee is pinned to
    /// it; known payload substitutions remain those of the scrutinee, since a
    /// pattern head selects a type, not the types of its per-value fields.
    fn check_pattern_type_agreement(
        &mut self,
        scrutinee: &Type,
        selected: &Type,
        head: &str,
        type_name: &str,
        span: brass_parser::Span,
    ) -> bool {
        let resolved = self.pattern_subject(scrutinee);
        if resolved.is_unknown() {
            let _ = self.solver.unify(scrutinee, selected);
            return true;
        }
        if !matches!((&resolved, selected),
            (Type::Sum(actual), Type::Sum(expected)) | (Type::Record(actual), Type::Record(expected))
                if actual.id == expected.id)
        {
            self.errors.push(TypeError {
                message: format!(
                    "pattern `{head}` names `{type_name}`, but the matched value has type `{}`",
                    resolved.display()
                ),
                span,
            });
            return false;
        }
        true
    }

    /// Check a `let`/`const` pattern: its shape, and that it always matches,
    /// since every binding it introduces must be initialized (see
    /// `check_irrefutable_pattern`).
    pub(super) fn check_let_pattern_against(
        &mut self,
        scrutinee: &Type,
        pat: &Pattern,
        value: &Expr,
        context: &str,
    ) {
        self.check_pattern_against(scrutinee, pat);
        self.check_irrefutable_pattern(scrutinee, pat, Some(value), context);
    }

    /// Report each part of `pat` that may fail to match a `scrutinee` value
    /// where every binding must be initialized (`context`: `let`, `const` or
    /// `for`). A literal, a qualified name, a unit variant, a variant of a sum
    /// with others, and any record or array pattern on a nullable subject are
    /// refutable. An array pattern is refutable on a growable slice, whose
    /// runtime length is not part of its type, unless `value` is an array
    /// literal of the pattern's length; fixed arrays and tuples carry an exact
    /// arity and destructure totally. Nested positions are checked too, so a
    /// slice inside a tuple or record cannot bypass the requirement.
    pub(super) fn check_irrefutable_pattern(
        &mut self,
        scrutinee: &Type,
        pat: &Pattern,
        value: Option<&Expr>,
        context: &str,
    ) {
        match pat {
            // A nullable subject may be absent, which no array or tuple
            // pattern matches.
            Pattern::Array(..)
                if matches!(peel_modes(&self.resolve(scrutinee)), Type::Nullable(_)) =>
            {
                self.report_refutable_pattern(pat, context)
            }
            Pattern::Array(patterns, span) => match self.resolve(scrutinee) {
                Type::Tuple(elements) => {
                    for (index, (pattern, element)) in patterns.iter().zip(&elements).enumerate() {
                        let item = match value {
                            Some(Expr::Array(items, _)) => items.get(index),
                            _ => None,
                        };
                        self.check_irrefutable_pattern(element, pattern, item, context);
                    }
                }
                Type::Array(element, _) => {
                    for (index, pattern) in patterns.iter().enumerate() {
                        let item = match value {
                            Some(Expr::Array(items, _)) => items.get(index),
                            _ => None,
                        };
                        self.check_irrefutable_pattern(&element, pattern, item, context);
                    }
                }
                Type::Slice(element) => {
                    let literal_items = match value {
                        Some(Expr::Array(items, _)) if items.len() == patterns.len() => Some(items),
                        _ => None,
                    };
                    if literal_items.is_none() {
                        self.errors.push(TypeError {
                            message: format!("cannot use a fixed-length array pattern in `{context}` with a growable array; use `if let` or `match`"),
                            span: *span,
                        });
                    }
                    for (index, pattern) in patterns.iter().enumerate() {
                        self.check_irrefutable_pattern(
                            &element,
                            pattern,
                            literal_items.and_then(|items| items.get(index)),
                            context,
                        );
                    }
                }
                _ => {
                    for pattern in patterns {
                        let ty = self.fresh_unknown();
                        self.check_irrefutable_pattern(&ty, pattern, None, context);
                    }
                }
            },
            Pattern::Record(variant, qualifier, fields, _) => {
                let ty = self.pattern_scrutinee_type(scrutinee, variant, qualifier.as_ref());
                if self.record_pattern_totality(&ty, variant) == Some(false) {
                    self.report_refutable_pattern(pat, context);
                }
                let field_types = self.pattern_field_types(&ty, variant);
                for field in fields {
                    if let Some(pattern) = &field.pat {
                        let field_ty = field_types
                            .get(&field.name)
                            .cloned()
                            .unwrap_or_else(|| self.fresh_unknown());
                        self.check_irrefutable_pattern(&field_ty, pattern, None, context);
                    }
                }
            }
            Pattern::Literal(..) => self.report_refutable_pattern(pat, context),
            Pattern::Binding(name, qualifier, _) => {
                if qualifier.is_some() || self.is_unit_variant_name(name) {
                    self.report_refutable_pattern(pat, context);
                }
            }
            Pattern::Wildcard(_) => {}
        }
    }

    fn report_refutable_pattern(&mut self, pat: &Pattern, context: &str) {
        self.errors.push(TypeError {
            message: format!("refutable pattern in `{context}`; use `if let` or `match`"),
            span: pat.span(),
        });
    }

    /// Reject arms following one total pattern and explain suspicious bindings.
    pub(super) fn check_unreachable_arms(
        &mut self,
        ty: &Type,
        arms: &[MatchArm],
        scopes: &ScopeStack,
    ) {
        let mut catch_all_note = None;
        for arm in arms {
            if let Some(note) = &catch_all_note {
                self.errors.push(TypeError {
                    message: format!("unreachable match arm{note}"),
                    span: arm.pattern.span(),
                });
            } else if self.match_pattern_is_total(ty, &arm.pattern) {
                catch_all_note = Some(self.catch_all_note(ty, &arm.pattern, scopes));
            }
        }
    }

    /// Determine coverage against the scrutinee, including nested field types.
    /// Unlike binding declarations, a match may cover a singleton unit sum.
    pub(super) fn match_pattern_is_total(&mut self, ty: &Type, pat: &Pattern) -> bool {
        let resolved = self.resolve(ty);
        match pat {
            Pattern::Wildcard(_) => true,
            Pattern::Binding(name, qualifier, _) => {
                if qualifier.is_none() && !self.is_unit_variant_name(name) {
                    return true;
                }
                matches!(peel_modes(&resolved), Type::Sum(sum)
                    if self.program.type_by_id(sum.id).is_some_and(|info|
                        matches!(&info.kind, TypeKind::Sum { variants }
                            if variants.len() == 1 && variants[0].name == *name)))
            }
            Pattern::Record(name, qualifier, fields, _) => {
                let ty = self.pattern_scrutinee_type(ty, name, qualifier.as_ref());
                if self.record_pattern_totality(&ty, name) != Some(true) {
                    return false;
                }
                let types = self.pattern_field_types(&ty, name);
                fields.iter().all(|field| {
                    field.pat.as_ref().is_none_or(|pat| {
                        let ty = types
                            .get(&field.name)
                            .cloned()
                            .unwrap_or_else(|| self.fresh_unknown());
                        self.match_pattern_is_total(&ty, pat)
                    })
                })
            }
            Pattern::Array(patterns, _) => match peel_modes(&resolved) {
                Type::Tuple(elements) => {
                    patterns.len() == elements.len()
                        && patterns
                            .iter()
                            .zip(elements)
                            .all(|(pat, ty)| self.match_pattern_is_total(ty, pat))
                }
                Type::Array(element, len) => {
                    patterns.len() == *len
                        && patterns
                            .iter()
                            .all(|pat| self.match_pattern_is_total(element, pat))
                }
                _ => false,
            },
            Pattern::Literal(..) => false,
        }
    }

    /// Explain the two common ways a name accidentally becomes a catch-all.
    pub(super) fn catch_all_note(&self, ty: &Type, pat: &Pattern, scopes: &ScopeStack) -> String {
        let Pattern::Binding(name, None, _) = pat else {
            return String::new();
        };
        if self.is_unit_variant_name(name) {
            return String::new();
        }
        let resolved = self.resolve(ty);
        let mut note = String::new();
        if let Type::Sum(sum) = peel_modes(&resolved)
            && let Some(info) = self.program.type_by_id(sum.id)
            && let TypeKind::Sum { variants } = &info.kind
            && let Some(variant) = variants
                .iter()
                .map(|v| (name_distance(name, &v.name), &v.name))
                .filter(|(distance, candidate)| {
                    *distance
                        <= if name.len().min(candidate.len()) < 3 {
                            1
                        } else {
                            2
                        }
                })
                .min()
                .map(|(_, name)| name)
        {
            note.push_str(&format!(
                "\nnote: `{name}` binds a new name; did you mean the variant `{variant}`?"
            ));
        }
        if self.pattern_shadows_constant(name, scopes) {
            note.push_str(&format!(
                "\nnote: `{name}` binds a new name and does not compare with the constant `{name}`"
            ));
        }
        note
    }

    fn pattern_shadows_constant(&self, name: &str, scopes: &ScopeStack) -> bool {
        // Local value scopes and const scopes both grow inward. A mutable local
        // or parameter hides a global constant of the same name.
        if let Some((depth, _)) = scopes
            .iter()
            .rev()
            .enumerate()
            .find(|(_, scope)| scope.contains_key(name))
            && depth + 1 < scopes.len()
        {
            return self
                .const_scopes
                .iter()
                .rev()
                .nth(depth)
                .is_some_and(|scope| scope.contains(name));
        }
        if !scopes.first().is_some_and(|scope| scope.contains_key(name)) {
            return false;
        }
        let binding_in = |path: &[String], remote: &str| {
            self.program
                .inits
                .iter()
                .find(|init| init.path == path)
                .and_then(|init| {
                    init.stmts.iter().rev().find_map(|stmt| {
                        let Stmt::Let { pat, is_const, .. } = stmt else {
                            return None;
                        };
                        let mut names = Vec::new();
                        self.collect_const_bindings(pat, &mut names);
                        names.iter().any(|n| n == remote).then_some(*is_const)
                    })
                })
        };
        if let Some(is_const) = binding_in(&self.current_module, name) {
            return is_const;
        }
        if let Some(origin) = self
            .program
            .import_origins
            .get(&self.current_module)
            .and_then(|imports| imports.get(name))
        {
            let remote = self
                .program
                .import_renames
                .get(&self.current_module)
                .and_then(|renames| renames.get(name))
                .map_or(name, String::as_str);
            return binding_in(origin, remote).unwrap_or(false);
        }
        self.program
            .prelude_modules
            .iter()
            .any(|path| binding_in(path, name) == Some(true))
    }

    /// Whether the record or variant pattern `name { .. }` (fields aside)
    /// covers every value of `ty`: a plain record or the variant of a
    /// single-variant sum does; a variant of a wider sum or any pattern on a
    /// nullable subject does not. An open subject can share a variant spelling
    /// across unrelated sums: `None` when those disagree, deferring the
    /// verdict to the check of the concrete instance.
    fn record_pattern_totality(&self, ty: &Type, name: &str) -> Option<bool> {
        let resolved = self.resolve(ty);
        let total = |info: &TypeInfo| matches!(&info.kind, TypeKind::Sum { variants } if variants.len() == 1);
        match peel_modes(&resolved) {
            Type::Sum(sum) => self.program.type_by_id(sum.id).map(total),
            Type::Nullable(_) => Some(false),
            // A head that is no variant here destructures a plain record.
            Type::Unknown(_) if !self.braced_head_is_variant(name, &resolved) => Some(true),
            Type::Unknown(_) => {
                let mut owners = self
                    .program
                    .variant_owner_ids(name)
                    .iter()
                    .filter_map(|id| self.program.type_by_id(*id));
                let Some(first) = owners.next() else {
                    return Some(true);
                };
                let first = total(first);
                owners.all(|info| total(info) == first).then_some(first)
            }
            _ => Some(true),
        }
    }

    /// The field types a record or variant pattern named `variant` binds over
    /// `ty` (its present value, when nullable): the scrutinee's nominal
    /// substitution, else the declared field type. An open subject takes them
    /// from the declaration of the sum that declares `variant`.
    pub(super) fn pattern_field_types(
        &mut self,
        ty: &Type,
        variant: &str,
    ) -> HashMap<String, Type> {
        let resolved = self.resolve(&self.pattern_subject(ty));
        if let Type::Record(record) = peel_modes(&resolved) {
            let Some(info) = self.program.type_by_id(record.id) else {
                return HashMap::default();
            };
            let TypeKind::Record { fields, .. } = &info.kind else {
                return HashMap::default();
            };
            return fields
                .iter()
                .map(|field| {
                    let ty = record
                        .substitution
                        .get(&field.name)
                        .cloned()
                        .or_else(|| field.resolved_ty.clone())
                        .unwrap_or_else(|| self.fresh_unknown());
                    (field.name.clone(), ty)
                })
                .collect();
        }
        if let Some((ok, err)) = resolved.result_payloads() {
            return match variant {
                "Ok" => HashMap::from_iter([("value".to_string(), ok.clone())]),
                "Err" => HashMap::from_iter([("error".to_string(), err.clone())]),
                _ => HashMap::default(),
            };
        }
        if let Type::Sum(name) = &resolved {
            return self
                .program
                .type_by_id(name.id)
                .and_then(|info| info.variant(variant))
                .map(|variant_info| {
                    variant_info
                        .fields
                        .iter()
                        .map(|field| {
                            let key = field_substitution_key(Some(variant), &field.name);
                            let ty = name
                                .substitution
                                .get(&key)
                                .cloned()
                                .or_else(|| field.resolved_ty.clone())
                                .unwrap_or_else(|| self.fresh_unknown());
                            (field.name.clone(), ty)
                        })
                        .collect()
                })
                .unwrap_or_default();
        }
        let sum_name = self.variant_owner(variant);
        let fields = sum_name
            .and_then(|name| self.program.types.get(&name))
            .and_then(|info| info.variant(variant))
            .map(|v| {
                v.fields
                    .iter()
                    .map(|f| (f.name.clone(), f.resolved_ty.clone()))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        fields
            .into_iter()
            .map(|(name, ty)| {
                let ty = ty.unwrap_or_else(|| self.fresh_unknown());
                (name, ty)
            })
            .collect()
    }
}

/// Levenshtein distance for the short identifiers used in variant suggestions.
fn name_distance(left: &str, right: &str) -> usize {
    let right: Vec<_> = right.chars().collect();
    let mut row: Vec<_> = (0..=right.len()).collect();
    for (i, a) in left.chars().enumerate() {
        let mut diagonal = row[0];
        row[0] = i + 1;
        for (j, b) in right.iter().enumerate() {
            let above = row[j + 1];
            row[j + 1] = (row[j] + 1)
                .min(above + 1)
                .min(diagonal + usize::from(a != *b));
            diagonal = above;
        }
    }
    row[right.len()]
}
