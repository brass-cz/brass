//! Pattern typing and nullable flow analysis: binding match/if-let
//! patterns against a scrutinee type, validating pattern shapes, and
//! the null-narrowing that tracks when a nullable binding is known
//! non-null (and when calls invalidate that knowledge).

use super::*;

impl<'a> Checker<'a> {
    pub(super) fn report_nullable_use(&mut self, span: brass_parser::Span) {
        self.errors.push(TypeError {
            message: "nullable value must be checked for null before use".to_string(),
            span,
        });
    }

    pub(super) fn apply_truthy_narrowing(&mut self, cond: &Expr, scopes: &mut ScopeStack) {
        if let Some(name) = narrow::truthy_narrows(cond) {
            self.narrow_non_null(name, scopes);
        }
    }

    pub(super) fn apply_guard_narrowing(&mut self, stmt: &Stmt, scopes: &mut ScopeStack) {
        let Stmt::Expr(Expr::If(cond, then, None, _)) = stmt else {
            return;
        };
        if !block_always_returns(then) {
            return;
        }
        if let Some(name) = narrow::falsy_narrows(cond) {
            self.narrow_non_null(name, scopes);
        }
    }

    fn narrow_non_null(&mut self, name: &str, scopes: &mut ScopeStack) {
        for scope in scopes.iter_mut().rev() {
            if let Some(original) = scope.get(name).cloned() {
                let Type::Nullable(inner) = self.resolve(&original) else {
                    return;
                };
                tracing::debug!(name, to = %inner.display(), "narrowing nullable to non-null");
                scope.insert(name.to_string(), (*inner).clone());
                // Remember the pre-narrowing type so a later call can undo the
                // narrowing when the binding is reachable by the callee (a
                // global or a closure-assigned local).
                self.narrowed_bindings
                    .push((name.to_string(), Type::Nullable(inner)));
                break;
            }
        }
    }

    /// Undo narrowings a call may have invalidated: a narrowed GLOBAL (frame 0
    /// of the scope stack; any callee can assign it) and a narrowed local that
    /// some closure in this body assigns (the closure may run during the call).
    /// The nullable type is restored in the current (branch-local) scope clone,
    /// so uses after the call must re-check for null. Plain locals stay
    /// narrowed: no callee can rebind them.
    pub(super) fn invalidate_narrowed_after_call(&mut self, scopes: &mut ScopeStack) {
        if self.narrowed_bindings.is_empty() {
            return;
        }
        let narrowed = self.narrowed_bindings.clone();
        for (name, original) in narrowed {
            let Some(frame_idx) = scopes.iter().rposition(|s| s.contains_key(&name)) else {
                continue;
            };
            let global = frame_idx == 0;
            if !global && !self.closure_write_targets.contains(&name) {
                continue;
            }
            let still_narrowed = scopes[frame_idx]
                .get(&name)
                .is_some_and(|t| !matches!(self.resolve(t), Type::Nullable(_)));
            if still_narrowed {
                tracing::debug!(name, "re-widening narrowed binding after call");
                scopes[frame_idx].insert(name.clone(), original.clone());
            }
        }
    }

    pub(super) fn bind_pattern(&mut self, pat: &Pattern, ty: &Type, scopes: &mut ScopeStack) {
        match pat {
            Pattern::Binding(name, span) => {
                if !self.is_unit_variant_name(name) {
                    scopes.last_mut().unwrap().insert(name.clone(), ty.clone());
                    self.record_binding(name, *span, ty);
                }
            }
            Pattern::Record(variant, fields, _) => {
                let field_types = self.pattern_field_types(ty, variant);
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
    /// name would accept or reject depending on hash order.
    fn scrutinee_accepts_variant(&mut self, scrutinee: &Type, variant: &str) -> bool {
        let resolved = self.resolve(scrutinee);
        if resolved.is_result_type() {
            return matches!(variant, "Ok" | "Err");
        }
        match resolved {
            Type::Sum(sum) => match self.program.type_by_id(sum.id) {
                Some(info) => info.variant(variant).is_some(),
                // No table entry (e.g. a synthesized sum): fall back to
                // matching the sum's name against the variant's possible owners.
                None => self
                    .program
                    .sums_containing_variant(variant)
                    .iter()
                    .any(|info| sum.is_name(&info.name)),
            },
            Type::Unknown(_) => true,
            _ => false,
        }
    }

    pub(super) fn check_pattern_against(&mut self, scrutinee: &Type, pat: &Pattern) {
        match pat {
            Pattern::Binding(name, span) => {
                if let Some(owner) = self.variant_owner(name)
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
            Pattern::Record(name, fields, span) => {
                let owner = self.variant_owner(name);
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
                        if owner.is_some() {
                            self.errors.push(TypeError {
                                message: format!("pattern `{name}` has no field `{}`", fp.name),
                                span: fp.span,
                            });
                        }
                        continue;
                    };
                    if let Some(subpat) = &fp.pat {
                        self.check_pattern_against(field_ty, subpat);
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
                        self.check_pattern_against(ety, pat);
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
                    .for_each(|pat| self.check_pattern_against(&elem, pat));
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

    /// Check a `let` pattern, whose bindings must always be initialized. Array
    /// patterns are refutable on a growable slice because its runtime length is
    /// not part of the type; those patterns belong in `if let` or `match`.
    /// Fixed arrays and tuples carry an exact arity and remain valid total
    /// destructures. Recurse so a slice nested in a tuple/record cannot bypass
    /// the same requirement.
    pub(super) fn check_let_pattern_against(
        &mut self,
        scrutinee: &Type,
        pat: &Pattern,
        value: &Expr,
    ) {
        self.check_pattern_against(scrutinee, pat);
        self.check_let_pattern_lengths(scrutinee, pat, Some(value));
    }

    fn check_let_pattern_lengths(&mut self, scrutinee: &Type, pat: &Pattern, value: Option<&Expr>) {
        match pat {
            Pattern::Array(patterns, span) => match self.resolve(scrutinee) {
                Type::Tuple(elements) => {
                    for (index, (pattern, element)) in patterns.iter().zip(&elements).enumerate() {
                        let item = match value {
                            Some(Expr::Array(items, _)) => items.get(index),
                            _ => None,
                        };
                        self.check_let_pattern_lengths(element, pattern, item);
                    }
                }
                Type::Array(element, _) => {
                    for (index, pattern) in patterns.iter().enumerate() {
                        let item = match value {
                            Some(Expr::Array(items, _)) => items.get(index),
                            _ => None,
                        };
                        self.check_let_pattern_lengths(&element, pattern, item);
                    }
                }
                Type::Slice(element) => {
                    let literal_items = match value {
                        Some(Expr::Array(items, _)) if items.len() == patterns.len() => Some(items),
                        _ => None,
                    };
                    if literal_items.is_none() {
                        self.errors.push(TypeError {
                            message: "cannot use a fixed-length array pattern in `let` with a growable array; use `if let` or `match`"
                                .to_string(),
                            span: *span,
                        });
                    }
                    for (index, pattern) in patterns.iter().enumerate() {
                        self.check_let_pattern_lengths(
                            &element,
                            pattern,
                            literal_items.and_then(|items| items.get(index)),
                        );
                    }
                }
                _ => {}
            },
            Pattern::Record(variant, fields, _) => {
                let field_types = self.pattern_field_types(scrutinee, variant);
                for field in fields {
                    if let Some(pattern) = &field.pat
                        && let Some(field_ty) = field_types.get(&field.name)
                    {
                        self.check_let_pattern_lengths(field_ty, pattern, None);
                    }
                }
            }
            Pattern::Binding(..) | Pattern::Wildcard(_) | Pattern::Literal(..) => {}
        }
    }

    pub(super) fn pattern_field_types(
        &mut self,
        ty: &Type,
        variant: &str,
    ) -> HashMap<String, Type> {
        let resolved = self.resolve(ty);
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
