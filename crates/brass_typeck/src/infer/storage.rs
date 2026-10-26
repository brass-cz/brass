//! Storage-site rules of value flow (types.md, "Structural subtyping").
//!
//! Structural subtyping is sound only where the receiving code is compiled
//! for the value's own type: a function or method parameter. Every other flow
//! site stores the value into a slot that keeps its declared type, so the
//! value must already have that representation
//! (`brass_typesys::same_representation`); a record conversion is explicit
//! (`T.from(v)`). This module holds the flow-site classification
//! ([`FlowSite`]), the diagnostic for a stored value whose representation
//! would change, and the one construction that adapts to its slot: an
//! anonymous record literal whose fields are exactly a declared record's is
//! built as that record, also as a branch value of an `if`, `match` or block
//! stored there. At a parameter, a wider literal stays structural while
//! matching fields receive the declared field requirements.

use super::*;

/// The kind of position a checked value flows into.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum FlowSite {
    /// An argument for a function or method parameter (annotated or not).
    /// The callee is instantiated at the argument's own type, so a value
    /// that is merely USABLE as the parameter type -- a record with more
    /// fields, a value satisfying a protocol record, an `A[]` whose records
    /// have the same fields as the annotation's -- is accepted as it is. A
    /// function value inside the argument is the exception: compiled once for
    /// its own signature, it must have the representation of the parameter's
    /// function type (`brass_typesys::function_values_keep_representation`).
    Parameter,
    /// Every other flow: an annotated `let`/`const`, an assignment, an
    /// annotated return, a record field or sum payload, an array or tuple
    /// element, a container slot pinned by its receiver (a map's key or
    /// value), and the arguments and result of a function-typed value. The
    /// slot keeps its declared type and is read back with no conversion, so
    /// the value must name the same record and sum declarations as the slot
    /// at every depth.
    /// A declared sum subtype is still accepted at the top level (the site
    /// rebuilds it as the parent), and so are numeric widening and nullable
    /// promotion, which the back ends perform at the flow point.
    Storage,
}

/// The declared record an anonymous record literal may be built as.
pub(super) struct LiteralTarget {
    /// The record's table symbol (`Program::types` key).
    symbol: String,
    /// The record's declared fields.
    fields: Vec<brass_hir::FieldInfo>,
}

impl<'a> Checker<'a> {
    /// Report a value that is usable where `want` is required but would
    /// change representation there: stored with another record or sum
    /// declaration (see [`FlowSite::Storage`]), or a function value whose
    /// signature names other declarations than the required function type.
    pub(super) fn report_storage_conversion(
        &mut self,
        got: &Type,
        want: &Type,
        span: brass_parser::Span,
    ) {
        let want_flow = brass_typesys::strip_nullable(want.clone());
        let (got_shown, want_shown) = brass_hir::mismatch_display(got, want);
        let message = match (peel_modes(got), peel_modes(&want_flow)) {
            (Type::Fun(..), Type::Fun(..)) => format!(
                "cannot use a `{got_shown}` where `{want_shown}` is required: a function value \
                 is compiled for its own signature, so its parameter and result types must \
                 name the same records and sums as the required function type"
            ),
            (got_value, Type::Record(w)) => {
                let hint = self.record_storage_hint(got_value, w);
                format!("cannot store a `{got_shown}` in a slot of type `{want_shown}`: {hint}")
            }
            _ => format!(
                "cannot store a `{got_shown}` in a slot of type `{want_shown}`: records and sums \
                 inside a stored value keep their own declaration and do not convert implicitly"
            ),
        };
        self.errors.push(TypeError { message, span });
    }

    /// Why a `got` value cannot be stored in a slot of record type `want`,
    /// with the explicit alternative.
    fn record_storage_hint(&self, got: &Type, want: &NominalType) -> String {
        let name = want.name();
        if want.id == brass_hir::STRUCTURAL_RECORD_ID {
            return "a slot of an anonymous record type holds only anonymous records with \
                    exactly its fields"
                .to_string();
        }
        if self.is_protocol_record(want) {
            return format!(
                "a `{name}` slot holds only `{name}` values; annotate a function parameter \
                 with `{name}` to accept any value that satisfies it"
            );
        }
        match got {
            Type::Record(g) if g.id == brass_hir::STRUCTURAL_RECORD_ID => format!(
                "an anonymous record does not convert implicitly; a record literal is built as \
                 `{name}` only when its fields are exactly `{name}`'s, otherwise use \
                 `{name}.from(value)`"
            ),
            Type::Record(_) => {
                format!("record values do not convert implicitly; use `{name}.from(value)`")
            }
            _ => format!("a `{name}` slot holds only `{name}` values"),
        }
    }

    /// Whether the declared record `n` is protocol-like: every member it
    /// requires is a method or a function-typed field taking `Self` first
    /// (`Display`, `Debug`, `Default`), so values satisfy it through their
    /// methods rather than by carrying its data.
    fn is_protocol_record(&self, n: &NominalType) -> bool {
        let Some(TypeKind::Record { fields, methods }) =
            self.program.type_by_id(n.id).map(|info| &info.kind)
        else {
            return false;
        };
        (!fields.is_empty() || !methods.is_empty())
            && fields.iter().all(|f| {
                matches!(&f.resolved_ty, Some(Type::Fun(params, _))
                    if matches!(params.first(), Some(Type::SelfType)))
            })
    }

    /// The declared record an anonymous record literal checked against
    /// `want` would be stored as: `want` (seen through passing modes and a
    /// nullable) when it names a declared record type.
    pub(super) fn anonymous_literal_target(&self, want: &Type) -> Option<LiteralTarget> {
        let want = brass_typesys::strip_nullable(peel_modes(&self.resolve(want)).clone());
        let Type::Record(n) = peel_modes(&want) else {
            return None;
        };
        if n.id < 0 {
            return None;
        }
        let info = self.program.type_by_id(n.id)?;
        let TypeKind::Record { fields, .. } = &info.kind else {
            return None;
        };
        Some(LiteralTarget {
            symbol: info.symbol.clone(),
            fields: fields.clone(),
        })
    }

    /// Check the anonymous record literal `expr` (fields `fields`) flowing
    /// into `want` at a site of kind `site`, when `want` names a declared
    /// record (`target`). A wider parameter literal stays structural while
    /// matching fields take the declaration's requirements. Returns `None`
    /// if the declared target cannot be resolved.
    ///
    /// A literal whose field names are exactly the record's is built AS that
    /// record: its fields are checked against the declaration like a written
    /// `Record { .. }` literal, and the record's symbol is recorded for the
    /// literal's span (the `type_names` channel) so lowering constructs the
    /// declared record rather than an anonymous one. Any other literal at a
    /// storage site is rejected here, naming the extra and missing fields.
    pub(super) fn check_anonymous_literal_against(
        &mut self,
        expr: &Expr,
        fields: &[(String, Expr)],
        target: LiteralTarget,
        want: &Type,
        site: FlowSite,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        let extra: Vec<&str> = fields
            .iter()
            .map(|(name, _)| name.as_str())
            .filter(|name| !target.fields.iter().any(|f| f.name == *name))
            .collect();
        let missing: Vec<&str> = target
            .fields
            .iter()
            .map(|f| f.name.as_str())
            .filter(|name| !fields.iter().any(|(field, _)| field == name))
            .collect();
        let span = expr.span();
        if extra.is_empty() && missing.is_empty() {
            let declared = info_type_ref(self.program, &target.symbol)?;
            // The requirement's own instance (a refinement alias pins open
            // fields and slots) is what the literal is built as.
            let pins = match brass_typesys::strip_nullable(peel_modes(&self.resolve(want)).clone())
            {
                Type::Record(n) => Some(n.substitution),
                _ => None,
            };
            let substitution = self.check_lit_fields(
                super::literals::LiteralShape {
                    who: &target.symbol,
                    variant: None,
                    declared: &target.fields,
                    pins: pins.as_ref(),
                },
                fields,
                span,
                scopes,
            );
            let ty = apply_nominal_substitution(declared, substitution);
            self.record_expr_type(expr, &ty);
            self.record_literal_nominal(span, target.symbol);
            self.expect_assignable_at(&ty, want, span, site);
            return Some(ty);
        }
        if site == FlowSite::Parameter {
            let required = brass_typesys::strip_nullable(peel_modes(&self.resolve(want)).clone());
            let Type::Record(record) = required else {
                return None;
            };
            let requirements = self.literal_field_requirements(&super::literals::LiteralShape {
                who: &target.symbol,
                variant: None,
                declared: &target.fields,
                pins: Some(&record.substitution),
            });
            let field_types = fields
                .iter()
                .map(|(name, value)| {
                    let ty = match requirements.get(name) {
                        Some(required) => self.check_expr_against(value, required, scopes),
                        None => self.check_expr(value, scopes),
                    };
                    (name.clone(), ty)
                })
                .collect();
            let ty = brass_hir::structural_record(field_types);
            self.record_expr_type(expr, &ty);
            self.expect_assignable_at(&ty, want, span, site);
            return Some(ty);
        }
        let got = self.check_expr(expr, scopes);
        let name = self.resolve(want);
        let name = brass_typesys::strip_nullable(peel_modes(&name).clone()).display();
        let mut differences = Vec::new();
        if !extra.is_empty() {
            differences.push(format!("unexpected field(s) `{}`", extra.join("`, `")));
        }
        if !missing.is_empty() {
            differences.push(format!("missing field(s) `{}`", missing.join("`, `")));
        }
        self.errors.push(TypeError {
            message: format!(
                "cannot store this record literal in a slot of type `{name}`: a literal is built \
                 as `{name}` only when its fields are exactly `{name}`'s ({})",
                differences.join("; ")
            ),
            span,
        });
        Some(got)
    }

    /// Whether `expr` is an anonymous record literal that `want` would build
    /// as a declared record (see [`Self::check_anonymous_literal_against`]).
    /// Flow sites that type their value before checking it against the
    /// requirement check such a literal against the requirement instead.
    pub(super) fn is_anonymous_literal_into(&self, expr: &Expr, want: &Type) -> bool {
        matches!(expr, Expr::TypeLit(name, _, _) if name.is_empty())
            && self.anonymous_literal_target(want).is_some()
    }

    /// The type a bare result value of a callable returning `want` flows
    /// into: the `Ok` payload of a (possibly nullable) `Result`, else `want`
    /// itself.
    pub(super) fn expression_body_result(&self, want: &Type) -> Type {
        let resolved = self.resolve(want);
        let result = match &resolved {
            Type::Nullable(inner) if inner.is_result_type() => inner.as_ref(),
            other => other,
        };
        match result.result_payloads() {
            Some((ok, _)) => ok.clone(),
            None => resolved,
        }
    }

    /// Check `value`, pushed or inserted into a slice whose element type is
    /// `elem`. A closed element requirement directs every construction;
    /// an open element is inferred from the value and committed through
    /// `expect_element_assignable`.
    pub(super) fn check_element_value(
        &mut self,
        value: &Expr,
        elem: &Type,
        scopes: &mut ScopeStack,
    ) {
        if self.solver.free_vars(&self.resolve(elem)).is_empty() {
            self.check_expr_against(value, elem, scopes);
            return;
        }
        let got = self.check_expr(value, scopes);
        self.expect_element_assignable(&got, elem, value);
    }

    /// Record that the anonymous record literal at `span` is built as the
    /// declared record `symbol`. A generic body whose instantiations would
    /// build the same literal as different records cannot be lowered once,
    /// so that is an error.
    pub(super) fn record_literal_nominal(&mut self, span: Span, symbol: String) {
        self.journal_elaboration(ElaborationJournalEntry::LiteralNominal(
            span,
            symbol.clone(),
        ));
        self.channel_changes
            .get_mut()
            .mark(channel_changes::Channel::TypeName, span);
        if let Some(prev) = self.type_names.insert(span, symbol.clone())
            && prev != symbol
        {
            self.errors.push(TypeError {
                message: format!(
                    "this record literal is built as `{prev}` in one instantiation of this \
                     generic function and as `{symbol}` in another, but one literal is built \
                     as one record type; construct the record where its type is known"
                ),
                span,
            });
        }
    }
}

/// The bare type reference of the declared type `symbol`.
fn info_type_ref(program: &Program, symbol: &str) -> Option<Type> {
    program.types.get(symbol).map(TypeInfo::type_ref)
}
