//! Assignability and operator typing: the `expect_*_assignable` family that
//! judges a value flow (numeric-literal adaptation, numeric and nullable
//! flow, directional structural subtyping, and the rebuild of a declared sum
//! subtype as its parent, recorded for MIR), the array-element storage
//! check, and the typing of unary and binary operators with their
//! diagnostics.
//!
//! A numeric literal adapts to the type it meets when its value fits: the
//! position it flows into, or the other operand of an operator (`b + 10` with
//! `b: uint8` is `uint8` and wraps). Otherwise an integer literal is `int32`
//! if it fits, else `int64`, else `uint64`, and a float literal `float64`.
//! `brass_typesys::operators` states the rule every pass shares.

use super::*;

impl<'a> Checker<'a> {
    /// Type the unary operator `op` over an operand of type `ty`. A reference
    /// or `mut` parameter is operated on through its value (`!x` on a
    /// `ref(T?)` is a null test like on a `T?`).
    pub(super) fn check_unary(&mut self, op: UnaryOp, ty: &Type, span: brass_parser::Span) -> Type {
        match peel_ref_mut(&self.resolve(ty)).clone() {
            Type::Nullable(_) => {
                if matches!(op, UnaryOp::Not) {
                    Type::Bool
                } else {
                    self.report_nullable_use(span);
                    self.fresh_unknown()
                }
            }
            Type::Int(k) if matches!(op, UnaryOp::Neg | UnaryOp::BitNot) => Type::Int(k),
            Type::Float(k) if matches!(op, UnaryOp::Neg) => Type::Float(k),
            Type::Bool if matches!(op, UnaryOp::Not) => Type::Bool,
            Type::Unknown(_) => self.fresh_unknown(),
            other => {
                self.errors.push(TypeError {
                    message: format!(
                        "operator `{}` is not defined for `{}`",
                        op.symbol(),
                        other.display()
                    ),
                    span,
                });
                self.fresh_unknown()
            }
        }
    }

    /// Type the binary operator `op` over its two operand expressions and
    /// their checked types. Numeric operands follow the shared operator rule
    /// (`brass_typesys::numeric_binary`): a literal operand adapts to the
    /// other operand's type when its value fits, otherwise both take their
    /// common type. Compound assignment `x op= e` comes through here
    /// with `x` as the left operand, so it is typed exactly as `x = x op e`.
    pub(super) fn check_binary_expr(
        &mut self,
        op: BinOp,
        left_expr: &Expr,
        left: &Type,
        right_expr: &Expr,
        right: &Type,
        span: brass_parser::Span,
    ) -> Type {
        // See through reference/mutability wrappers: an operand read through a
        // reference (e.g. a `ref(mut(int32))` array element bound by a `for` loop)
        // operates on its underlying value, and the operator yields that value type.
        let left = peel_ref_mut(&self.resolve(left)).clone();
        let right = peel_ref_mut(&self.resolve(right)).clone();
        if matches!(left, Type::Nullable(_)) || matches!(right, Type::Nullable(_)) {
            if is_null_comparison(op, &left, &right) {
                return Type::Bool;
            }
            self.report_nullable_use(span);
            return self.fresh_unknown();
        }
        let (left_literal, right_literal) = (
            brass_typesys::NumericLiteral::of_expr(left_expr),
            brass_typesys::NumericLiteral::of_expr(right_expr),
        );
        let numeric = brass_typesys::numeric_binary(
            op,
            brass_typesys::NumericOperand::new(&left, left_literal),
            brass_typesys::NumericOperand::new(&right, right_literal),
        );
        match numeric {
            Ok(typing) => return typing.result,
            Err(brass_typesys::OperatorError::NotNumeric) => {}
            Err(_) => return self.binary_error(op, &left, &right, span),
        }
        // A closure parameter still being inferred next to a numeric
        // LITERAL: the literal adapts to whatever the argument turns out to
        // be, so the operation is typed by the parameter itself -- `(x) -> x
        // * 2` returns its argument's type at every instantiation instead of
        // the literal's default `int32`.
        // A FLOAT literal adapts only to a float argument: next to an integer
        // the operation is computed in `float64`. Its type is then not the
        // parameter's, nor one fixed type; it stays open, and each
        // application's check of the body at the argument's type answers.
        let follows =
            |t: &Type| matches!(t, Type::Unknown(id) if self.closure_param_vars.contains(id));
        use brass_typesys::NumericLiteral;
        let result = match (&left, &right, left_literal, right_literal) {
            (Type::Unknown(_), Type::Float(_), _, Some(NumericLiteral::Float(_)))
                if arithmetic_follows_operand(op) && follows(&left) =>
            {
                self.fresh_unknown()
            }
            (Type::Float(_), Type::Unknown(_), Some(NumericLiteral::Float(_)), _)
                if arithmetic_follows_operand(op) && follows(&right) =>
            {
                self.fresh_unknown()
            }
            (Type::Unknown(_), Type::Int(_) | Type::Float(_), _, Some(_))
                if arithmetic_follows_operand(op) && follows(&left) =>
            {
                left.clone()
            }
            (Type::Int(_) | Type::Float(_), Type::Unknown(_), Some(_), _)
                if arithmetic_follows_operand(op) && follows(&right) =>
            {
                right.clone()
            }
            _ => self.non_numeric_binary(op, &left, &right, span),
        };
        // An operand still being inferred (a closure parameter) must accept
        // what this typing assumed of it once its type is known.
        self.record_binary_shape(op, (&left, left_literal), (&right, right_literal), &result);
        result
    }

    /// The non-numeric pairs of [`Self::check_binary_expr`]: string
    /// concatenation and equality, bools, records, and operands whose type is
    /// still being inferred.
    fn non_numeric_binary(
        &mut self,
        op: BinOp,
        left: &Type,
        right: &Type,
        span: brass_parser::Span,
    ) -> Type {
        let (left, right) = (left.clone(), right.clone());
        let is_unknown = matches!(left, Type::Unknown(_)) || matches!(right, Type::Unknown(_));
        match op {
            BinOp::Add if matches!((&left, &right), (Type::Str, Type::Str)) => Type::Str,
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                if is_unknown {
                    // One operand is still an open inference variable. The result
                    // takes the *other* operand's numeric type when it is a known
                    // number, so a value flowing only through `x + 1` is concretely
                    // typed (a count read back as `int32`) and a store of it pins
                    // the destination. The open variable itself is not committed
                    // here -- a concrete re-elaboration may make it `float64` -- so
                    // numeric polymorphism is preserved.
                    match (&left, &right) {
                        (Type::Unknown(_), Type::Int(_) | Type::Float(_)) => right.clone(),
                        (Type::Int(_) | Type::Float(_), Type::Unknown(_)) => left.clone(),
                        _ => self.fresh_unknown(),
                    }
                } else {
                    self.binary_error(op, &left, &right, span)
                }
            }
            BinOp::Eq | BinOp::Ne => {
                if self.can_unify(&left, &right)
                    || matches!(left, Type::Never)
                    || matches!(right, Type::Never)
                {
                    Type::Bool
                } else {
                    self.binary_error(op, &left, &right, span)
                }
            }
            // Ordering comparisons are numeric only. Strings have
            // no ordering: `==`/`!=` compare them, but `<`/`>`/`<=`/`>=` do not.
            BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                if is_unknown {
                    Type::Bool
                } else {
                    self.binary_error(op, &left, &right, span)
                }
            }
            BinOp::And | BinOp::Or => match (&left, &right) {
                (Type::Bool, Type::Bool) => Type::Bool,
                (Type::Unknown(_), _) | (_, Type::Unknown(_)) => Type::Bool,
                _ => self.binary_error(op, &left, &right, span),
            },
            // Remainder, bitwise and shift operators are integer-only.
            BinOp::Rem | BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
                if is_unknown {
                    self.fresh_unknown()
                } else {
                    self.binary_error(op, &left, &right, span)
                }
            }
        }
    }

    fn binary_error(
        &mut self,
        op: BinOp,
        left: &Type,
        right: &Type,
        span: brass_parser::Span,
    ) -> Type {
        self.errors.push(TypeError {
            message: format!(
                "operator `{}` is not defined for `{}` and `{}` (no applicable conversion)",
                op.symbol(),
                left.display(),
                right.display()
            ),
            span,
        });
        self.fresh_unknown()
    }

    /// A flow site just accepted `got` where `want` is required through the
    /// structural path. When that acceptance is a declared sum subtype (two
    /// different sum nominals related by `type Child: Parent`), the value must
    /// be REBUILT as the parent at runtime -- the child's variant payloads are
    /// wider, so identity flow would misread the unboxed layout. Record the
    /// site for MIR lowering, and bind the payload slots the required
    /// instance leaves open to the value's own (what unification would have
    /// done had the nominals matched), so an `infer!` return's payloads
    /// resolve from the coerced value.
    pub(super) fn record_sum_view(&mut self, got: &Type, want: &Type, span: brass_parser::Span) {
        let (Type::Sum(have), Type::Sum(target)) = (got, want) else {
            return;
        };
        if have.id == target.id {
            return;
        }
        // The value's payload for a slot comes from its substitution (an
        // unannotated field recorded at construction) or its declaration (an
        // annotated field, which carries no substitution entry).
        let declared = |key: &str| -> Option<Type> {
            let (vname, fname) = key.split_once('.')?;
            let info = self.program.type_by_id(have.id)?;
            let TypeKind::Sum { variants } = &info.kind else {
                return None;
            };
            variants
                .iter()
                .find(|v| v.name == vname)?
                .fields
                .iter()
                .find(|f| f.name == fname)?
                .resolved_ty
                .clone()
                .filter(|t| !t.is_unknown())
        };
        for (key, wt) in target.substitution.iter() {
            if !self.resolve(wt).is_unknown() {
                continue;
            }
            let ht = have
                .substitution
                .get(key)
                .cloned()
                .filter(|t| !self.resolve(t).is_unknown())
                .or_else(|| declared(key));
            if let Some(ht) = ht {
                let _ = self.solver.unify(wt, &ht);
            }
        }
        let resolved = self.resolve(want);
        self.record_sum_view_type(span, resolved);
    }

    /// Record that the value at `span` is rebuilt as the parent sum instance
    /// `view` (the `sum_views` channel), checked against the other
    /// instantiations' lowering of the same span (see `note_sum_view`).
    pub(super) fn record_sum_view_type(&mut self, span: brass_parser::Span, view: Type) {
        self.journal_elaboration(ElaborationJournalEntry::SumView(span, view.clone()));
        self.note_sum_view(span, Some(&view));
        self.channel_changes
            .get_mut()
            .mark(channel_changes::Channel::SumView, span);
        self.sum_views.insert(span, view);
    }

    /// Evidence that the sum flow at `span` needs NO rebuild in this
    /// elaboration (the value already has the required nominal). Recorded so
    /// a generic body where another instantiation coerces at the same span is
    /// rejected instead of executing the baked rebuild on an uncoerced value.
    pub(super) fn record_sum_view_identity(&mut self, span: brass_parser::Span) {
        self.journal_elaboration(ElaborationJournalEntry::SumViewIdentity(span));
        self.note_sum_view(span, None);
    }

    /// Retain each observation of a sum flow's lowering, including open
    /// payloads. Inference variables carry no layout evidence until resolved;
    /// the known parts must agree with every other observation of this span.
    fn note_sum_view(&mut self, span: brass_parser::Span, view: Option<&Type>) {
        if self.sum_view_poisoned.contains(&span) {
            return;
        }
        if view.is_some_and(|ty| !matches!(ty, Type::Sum(_))) {
            return;
        }
        let view = view.cloned();
        let seen = self.sum_view_seen.entry(span).or_default();
        if !seen.contains(&view) {
            seen.push(view);
        }
        self.check_sum_view_observations(span);
    }

    /// Recheck retained sum-flow evidence after all payload constraints settle.
    pub(super) fn settle_sum_views(&mut self) {
        let spans: Vec<_> = self.sum_view_seen.keys().copied().collect();
        for span in spans {
            self.check_sum_view_observations(span);
        }
    }

    fn check_sum_view_observations(&mut self, span: brass_parser::Span) {
        if self.sum_view_poisoned.contains(&span) {
            return;
        }
        let views: Vec<_> = self.sum_view_seen[&span]
            .iter()
            .map(|view| view.as_ref().map(|ty| self.resolve(ty)))
            .collect();
        for (index, previous) in views.iter().enumerate() {
            for view in &views[index + 1..] {
                let message = match (previous, view) {
                    (None, None) => continue,
                    (Some(p), Some(n)) if sum_view_layouts_agree(p, n) => continue,
                    (Some(_), Some(_)) => {
                        "this value coerces to different parent sum \
                         instantiations across instantiations of this generic function; the \
                         shared lowering can only rebuild one shape (annotate the parameter \
                         to fix it)"
                    }
                    _ => {
                        "this value coerces to a declared parent sum in one instantiation \
                         of this generic function and flows unchanged in another; the two \
                         lower differently (annotate the parameter to fix it)"
                    }
                };
                self.errors.push(TypeError {
                    message: message.to_string(),
                    span,
                });
                self.sum_view_poisoned.insert(span);
                return;
            }
        }
    }

    /// [`Self::expect_expr_assignable_at`] for a storage site.
    pub(super) fn expect_expr_assignable(&mut self, got: &Type, want: &Type, expr: &Expr) {
        self.expect_expr_assignable_at(got, want, expr, FlowSite::Storage);
    }

    /// [`Self::expect_assignable_at`] for the value expression `expr`: an
    /// integer or float literal that fits the required numeric type adapts
    /// to it instead of being checked as its default kind.
    pub(super) fn expect_expr_assignable_at(
        &mut self,
        got: &Type,
        want: &Type,
        expr: &Expr,
        site: FlowSite,
    ) {
        if integer_literal_fits(expr, want) {
            return;
        }
        if self.check_float_literal(expr, want) || self.report_unfit_int_literal(expr, want) {
            return;
        }
        self.expect_assignable_at(got, want, expr.span(), site);
    }

    /// Report an integer literal written into a numeric position whose type
    /// cannot hold its value (`let b: int8 = 300`, `let f: float32 =
    /// 16777217`), naming the literal rather than its default type. A literal
    /// never converts lossily, so this is the whole verdict for such a flow;
    /// returns whether `expr` was that case.
    fn report_unfit_int_literal(&mut self, expr: &Expr, want: &Type) -> bool {
        let Some(value) = expr.int_literal_value() else {
            return false;
        };
        let target = peel_position(&self.resolve(want)).clone();
        let reason = match target {
            Type::Int(_) => "its value is out of range",
            Type::Float(_) => "the float cannot represent its value exactly",
            _ => return false,
        };
        self.errors.push(TypeError {
            message: format!(
                "integer literal `{value}` does not fit `{}`: {reason}",
                target.display()
            ),
            span: expr.span(),
        });
        true
    }

    /// Adapt a float literal to its contextual width, allowing rounding and
    /// underflow but reporting overflow at the literal rather than its binding.
    fn check_float_literal(&mut self, expr: &Expr, want: &Type) -> bool {
        let literal = match expr {
            Expr::Unary(UnaryOp::Neg, inner, _) => inner.as_ref(),
            other => other,
        };
        let Expr::Float(value, span) = literal else {
            return false;
        };
        let mut want = self.resolve(want);
        loop {
            match want {
                Type::Nullable(inner)
                | Type::Ref(inner)
                | Type::Mut(inner)
                | Type::ConstOf(inner) => {
                    want = self.resolve(&inner);
                }
                Type::Float(kind) => {
                    if kind == FloatKind::F32 && !(*value as f32).is_finite() {
                        self.errors.push(TypeError {
                            message: "float literal out of range for float32".into(),
                            span: *span,
                        });
                    }
                    return true;
                }
                _ => return false,
            }
        }
    }

    /// Commit equality information produced by a write into typed storage.
    /// Ordinary assignability probes are intentionally non-committing so a
    /// polymorphic value may be checked at several call sites. A value that is
    /// stored is different: an open closure parameter written into `int32`
    /// storage is itself constrained to `int32`, and every later call must see
    /// that constraint. A failed attempt is rolled back; the normal
    /// assignability check remains responsible for its diagnostic.
    pub(super) fn constrain_stored_value(&mut self, got: &Type, storage: &Type) -> bool {
        if self.solver.free_vars(&self.resolve(got)).is_empty() {
            return false;
        }
        let snapshot = self.solver.snapshot();
        if self.solver.unify(got, storage).is_ok() {
            return true;
        }
        self.solver.rollback(snapshot);
        false
    }

    /// Commit `got` to `want` when every variable `got` still has is an empty
    /// array literal's element and `want` is fully known (see
    /// [`Self::expect_assignable_at`]). A failed unification is rolled back
    /// and left to the ordinary flow check.
    fn pins_empty_array_elems(&mut self, got: &Type, want: &Type) -> bool {
        let free = self.solver.free_vars(got);
        if free.is_empty()
            || !brass_hir::is_fully_known(want)
            || !free
                .iter()
                .all(|id| self.solver.kind_of(*id) == Some(InferenceVarKind::EmptyArrayElem))
        {
            return false;
        }
        let snapshot = self.solver.snapshot();
        if self.solver.unify(got, want).is_ok() {
            return true;
        }
        self.solver.rollback(snapshot);
        false
    }

    /// [`Self::expect_assignable_at`] for a storage site.
    pub(super) fn expect_assignable(&mut self, got: &Type, want: &Type, span: brass_parser::Span) {
        self.expect_assignable_at(got, want, span, FlowSite::Storage);
    }

    /// Check that a `got` value is usable where `want` is required at a flow
    /// site of kind `site`, reporting a diagnostic otherwise. The accept/reject
    /// core is the shared value-flow rule in `brass_typesys` (nullable-stripped
    /// unification plus numeric widening), layered here with the infer pass's
    /// own concerns: sum-view recording for MIR, directional structural
    /// subtyping (admitted as is at a parameter, only without a change of
    /// representation at a storage site -- see [`FlowSite`]), and the rich
    /// per-case diagnostics (nullable use, narrowing hints, mismatch display).
    pub(super) fn expect_assignable_at(
        &mut self,
        got: &Type,
        want: &Type,
        span: brass_parser::Span,
        site: FlowSite,
    ) {
        let got = self.resolve(got);
        let want = self.resolve(want);
        // A type-test probe hole takes the first concrete requirement the
        // tested arm places on the subject. Assignability otherwise never
        // pins a probed value, but the hole EXISTS to be pinned: it is what
        // makes `if v: infer { to_bytes(v) }` read as "the type `to_bytes`
        // accepts". Commit-and-accept; the whole probe is rolled back by the
        // type-test checker afterwards.
        if !self.type_test_holes.is_empty()
            && let Type::Unknown(id) = &got
            && self.type_test_holes.contains(id)
            && brass_hir::is_fully_known(&want)
            && self.solver.unify(&got, &want).is_ok()
        {
            return;
        }
        // An unconstrained inference variable whose type cannot be inferred
        // reaching a concrete required position is an error rather than a silent
        // unification: a bare empty array carries no
        // element, and a function that only returns `error(...)` has no `Ok`
        // payload type. A `want` that is itself unknown leaves the contract
        // deferred rather than wrong.
        if let Type::Unknown(id) = &got
            && !want.is_unknown()
        {
            match self.solver.kind_of(*id) {
                Some(InferenceVarKind::EmptyArrayElem) => {
                    self.errors.push(TypeError {
                        message: "cannot infer element type of empty array; add a type annotation"
                            .to_string(),
                        span,
                    });
                    return;
                }
                Some(InferenceVarKind::ErrorOnlyOk | InferenceVarKind::UninhabitedOk) => {
                    self.errors.push(TypeError {
                        message: "cannot infer the Ok payload type of a function that only \
                                      returns errors; add a non-error return or an annotation"
                            .to_string(),
                        span,
                    });
                    return;
                }
                _ => {}
            }
        }
        // Nullability is a property of the value, not of how it is passed:
        // a `ref(mut(T?))` position takes a `T?` (and `null`) exactly like a
        // `T?` one, and a reference to a `T?` is as nullable as the `T?`.
        let got_value = peel_ref_mut(&got);
        let want_value = peel_ref_mut(&want);
        if got_value.is_null() && !matches!(want_value, Type::Nullable(_)) {
            self.errors.push(TypeError {
                message: format!(
                    "cannot use `{}` where `{}` is required",
                    got.display(),
                    want.display()
                ),
                span,
            });
            return;
        }
        // A nullable value in a required non-null position must be narrowed
        // first -- unless the requirement is still an open variable (an
        // unannotated closure parameter), which the nullable simply pins, the
        // way passing it to an unannotated function parameter does.
        if matches!(got_value, Type::Nullable(_))
            && !matches!(want_value, Type::Nullable(_))
            && !want_value.is_unknown()
        {
            self.report_nullable_use(span);
            return;
        }
        // The value-flow view of the requirement: a `T?` position accepts
        // whatever its `T` accepts (the store wraps the converted value).
        let want_flow = brass_typesys::strip_nullable(want.clone());
        // A declared sum subtype flowing into its parent must be RECORDED so
        // MIR rebuilds the value -- the structural fallback below would
        // otherwise accept it silently and the unboxed layout would be
        // misread. Checked before the general acceptance paths, against the
        // nullable-stripped requirement (`Result<..>?` still coerces the sum).
        if let (Type::Sum(h), Type::Sum(w)) = (&got, &want_flow) {
            if h.id != w.id && crate::structural::types_compatible(self.program, &got, &want_flow) {
                self.record_sum_view(&got, &want_flow, span);
                return;
            }
            if h.id == w.id {
                // Same-nominal flow: no rebuild here, and another
                // instantiation must not bake one at this span.
                self.record_sum_view_identity(span);
            }
        }
        // An empty array literal's element type is fixed by the first fully
        // known slot or parameter it flows into: the value stored or passed
        // IS that array, so the requirement decides its element (bracket
        // literal rule 1) rather than leaving it to a back end to re-derive.
        if self.pins_empty_array_elems(&got, &want_flow) {
            return;
        }
        // Core value-flow acceptance, delegated to the shared authority
        // (`brass_typesys::flow_probe`): nullable-stripping unification,
        // probed without committing -- an assignability check must not pin a
        // polymorphic value probed at several sites (a store that should
        // constrain the value commits through `constrain_stored_value`).
        if brass_typesys::flow_probe(&mut self.solver, &got, &want) {
            return;
        }
        // Automatic numeric conversion: a numeric value flows into a numeric
        // position of another type (int widths/signedness, int -> float),
        // also through a nullable requirement; the back ends convert at the
        // flow point. float -> int stays explicit.
        if numeric_flows_into(&got, &want_flow) {
            return;
        }
        // Structural subtyping, one direction only: the value must be usable
        // AS the requirement, checked against both the requirement and its
        // nullable-stripped view (a wider record also flows into a `T?`
        // parameter, where unification alone would refuse the nullable). A
        // parameter takes the value as it is -- its callee is instantiated at
        // the argument's own type -- except for the function values it holds,
        // which are compiled once for their own signatures; a storage site
        // keeps its declared type, so the value must already have that
        // representation throughout.
        if self.structural_flow_accepts(&got, &want)
            || (want_flow != want && self.structural_flow_accepts(&got, &want_flow))
        {
            let keeps_representation = match site {
                FlowSite::Parameter => {
                    brass_typesys::function_values_keep_representation(&got, &want)
                }
                FlowSite::Storage => brass_typesys::same_representation(&got, &want),
            };
            if keeps_representation {
                return;
            }
            self.report_storage_conversion(&got, &want, span);
            return;
        }
        // A numeric pair that is not value-preserving gets the dedicated
        // narrowing diagnostic with the explicit-conversion hint from the
        // flow authority.
        if let brass_typesys::Flow::Forbidden(hint) = brass_typesys::numeric_flow(&got, &want)
            && !hint.is_empty()
        {
            self.errors.push(TypeError {
                message: format!(
                    "cannot implicitly convert `{}` to `{}`: {hint} (`{}.from(x)`)",
                    got.display(),
                    want.display(),
                    want.display(),
                ),
                span,
            });
            return;
        }
        let (got, want) = brass_hir::mismatch_display(&got, &want);
        self.errors.push(TypeError {
            message: format!("cannot use `{got}` where `{want}` is required"),
            span,
        });
    }

    /// Whether `got` is usable where `want` is required under structural
    /// record subtyping (`brass_typesys::types_compatible`). Directional: a
    /// record with fewer fields never flows into a position requiring more.
    fn structural_flow_accepts(&self, got: &Type, want: &Type) -> bool {
        crate::structural::types_compatible(self.program, got, want)
    }

    /// Check a value pushed/inserted into a slice against its element type. The
    /// element is storage, so the value must be usable *as* the element AND
    /// keep its representation: a structural relative of the element type is
    /// rejected and cannot corrupt the unboxed element layout. When the element
    /// type is still an open inference variable it is pinned to the value
    /// through `solver.unify`, so the occurs check fires -- pushing an array
    /// into itself (`a.push(a)`) is reported here instead of leaving the
    /// element unbound to be mistyped at the call site.
    pub(super) fn expect_element_assignable(&mut self, got: &Type, elem: &Type, expr: &Expr) {
        let got = self.resolve(got);
        let want = self.resolve(elem);
        if integer_literal_fits(expr, &want) || self.report_unfit_int_literal(expr, &want) {
            return;
        }
        // The element type carries an open inference variable -- either it is one
        // (a fresh `?[]`) or it is a record/array with open components (an
        // `_Entry<?, ?>` element whose key/value are not yet fixed). Pin it to the
        // value by committing the unification, so the stored value's concrete type
        // refines the element through the solver's record/array unification.
        if !self.solver.free_vars(&want).is_empty() {
            // Pushing/storing `null` into a still-open element makes the element a
            // *nullable with an open inner* (`Nullable(?)`), rather than collapsing
            // it to `Nullable(Never)`. This is what lets a slot array seeded with
            // `null` (`entries.push(null)`) still take its element type from the
            // non-null values stored later: the open inner is refined below.
            if got.is_null() && matches!(want, Type::Unknown(_)) {
                let inner = self.fresh_unknown();
                let _ = self.solver.unify(elem, &Type::Nullable(Box::new(inner)));
                return;
            }
            // A non-null value stored into a nullable element refines the element's
            // *inner* type (a concrete `_Entry<K, V>` into a `_Entry?[]` slot pins
            // `K` and `V`), so a nullable container fixes its element from the
            // values inserted while still accepting `null`. Otherwise the value
            // refines the element directly.
            let snapshot = self.solver.snapshot();
            let outcome = match &want {
                Type::Nullable(inner) if !got.is_null() && !matches!(got, Type::Nullable(_)) => {
                    self.solver.unify(inner, &got)
                }
                _ => self.solver.unify(elem, &got),
            };
            if outcome.is_err() {
                self.solver.rollback(snapshot);
                if want.is_unknown() {
                    // The only hard failure on a *bare* element variable is the occurs
                    // check: pushing the array into itself, an infinite element type.
                    self.errors.push(TypeError {
                        message: "cannot push a value whose type contains this array; \
                                  the element type would be infinite"
                            .to_string(),
                        span: expr.span(),
                    });
                }
            }
            // A failure against a *partially* fixed element (a record/array with
            // open components) is left to defer rather than reported: the store may
            // go through a witness alias the body itself re-reads
            // (`HashMap._grow` re-inserts the pairs of `old_entries`), which is
            // loose by construction.
            // A genuine clash on a fully concrete element is caught by the concrete
            // path below, which still runs because such an element has no free var.
            return;
        }
        if self.constrain_stored_value(&got, &want) {
            return;
        }
        if got.is_null() && !matches!(want, Type::Nullable(_)) {
            self.report_element_mismatch(&got, &want, expr.span());
            return;
        }
        if matches!(got, Type::Nullable(_)) && !matches!(want, Type::Nullable(_)) {
            self.report_nullable_use(expr.span());
            return;
        }
        if let Type::Nullable(inner) = &want
            && (self.element_assignable_into(&got, inner) || matches!(got, Type::Never))
        {
            return;
        }
        if self.element_assignable_into(&got, &want) {
            return;
        }
        let want_flow = brass_typesys::strip_nullable(want.clone());
        // A declared sum subtype is stored rebuilt as its parent, as at every
        // other value flow site (see `expect_assignable_at`).
        if let (Type::Sum(h), Type::Sum(w)) = (&got, &want_flow)
            && h.id != w.id
            && crate::structural::declares_sum_parent(self.program, h.id, w.id, 0)
        {
            self.record_sum_view(&got, &want_flow, expr.span());
            return;
        }
        // Usable as the element, but of another record/sum declaration: name
        // the representation change rather than a plain mismatch.
        if crate::structural::types_compatible(self.program, &got, &want_flow) {
            self.report_storage_conversion(&got, &want, expr.span());
            return;
        }
        self.report_element_mismatch(&got, &want, expr.span());
    }

    /// Assignability into array-element storage. Elements are read back at the
    /// array's element type AND overwritten through it, so the position is
    /// invariant: a structural *width* supertype (a record with extra fields,
    /// hence a different layout) must not be stored where the narrower element
    /// type is expected -- reading it back would reinterpret the wider layout.
    /// Mutual compatibility alone still relates two declarations with the same
    /// fields, so the element must also keep its representation.
    /// One-directional `types_compatible` is only sound for consumed positions
    /// (arguments), not for shared mutable storage. A number is different: it
    /// is converted on the way in, so the value-preserving numeric flow
    /// conversions apply (`an_int32` pushed into an `int64[]` widens).
    fn element_assignable_into(&self, got: &Type, want: &Type) -> bool {
        Subst::new().unify(got, want).is_ok()
            || numeric_flows_into(got, want)
            || (crate::structural::types_invariant(self.program, got, want)
                && brass_typesys::same_representation(got, want))
    }

    fn report_element_mismatch(&mut self, got: &Type, want: &Type, span: brass_parser::Span) {
        let (got, want) = brass_hir::mismatch_display(got, want);
        self.errors.push(TypeError {
            message: format!("cannot use `{got}` where `{want}` is required"),
            span,
        });
    }
}

/// Whether `expr` is an integer literal (`5`, `-128`) whose value fits the
/// numeric position `want` (`brass_typesys::literal_fits`: an integer range
/// holding it, or a float representing it exactly), seen through a nullable
/// cell and the passing-mode wrappers: assigning a literal to a
/// `ref(mut(int32))` element (an array index through a mutable reference)
/// targets the underlying `int32`. A fitting literal takes the position's
/// type instead of its default, so `let m: int8 = -128` is no narrowing and
/// `let e: float32 = 3` is the float `3.0`.
pub(super) fn integer_literal_fits(expr: &Expr, want: &Type) -> bool {
    expr.int_literal_value()
        .is_some_and(|value| brass_typesys::literal_fits(value, peel_position(want)))
}

/// A position's value type: `want` with every nullable and passing-mode
/// wrapper removed.
fn peel_position(want: &Type) -> &Type {
    match want {
        Type::Nullable(inner) | Type::Ref(inner) | Type::Mut(inner) | Type::ConstOf(inner) => {
            peel_position(inner)
        }
        other => other,
    }
}

/// The join of two branch or return types when at least one is the type of
/// `null` (`never?`): `null` with `null` stays `never?`, and `null` with `T`
/// is `T?` (a nullable or still-open `T` as it is). `None` when neither side
/// is `null`.
pub(super) fn common_nullable_type(left: &Type, right: &Type) -> Option<Type> {
    match (left.is_null(), right.is_null()) {
        (true, true) => Some(Type::null()),
        (true, false) => Some(nullable_common_side(right)),
        (false, true) => Some(nullable_common_side(left)),
        (false, false) => None,
    }
}

fn nullable_common_side(ty: &Type) -> Type {
    match ty {
        Type::Unknown(_) | Type::Nullable(_) => ty.clone(),
        other => Type::Nullable(Box::new(other.clone())),
    }
}

/// Whether the result of `op` is its operands' (common) type, so an operand
/// next to an adapting literal determines it alone. Comparisons yield `bool`
/// and logical operators take `bool` operands.
fn arithmetic_follows_operand(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Rem
            | BinOp::BitAnd
            | BinOp::BitOr
            | BinOp::BitXor
            | BinOp::Shl
            | BinOp::Shr
    )
}

/// Whether resolved observations contain compatible layout evidence. Open
/// leaves constrain nothing; nominal slots present on only one side add
/// information. Structural record field sets and function signatures retain
/// their own shapes even when some component types are still open.
fn sum_view_layouts_agree(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Unknown(_) | Type::Never | Type::SelfType, _)
        | (_, Type::Unknown(_) | Type::Never | Type::SelfType) => true,
        (Type::Array(a, al), Type::Array(b, bl)) => al == bl && sum_view_layouts_agree(a, b),
        (Type::Slice(a), Type::Slice(b))
        | (Type::Nullable(a), Type::Nullable(b))
        | (Type::ConstOf(a), Type::ConstOf(b))
        | (Type::Mut(a), Type::Mut(b))
        | (Type::Ref(a), Type::Ref(b)) => sum_view_layouts_agree(a, b),
        (Type::Fun(ap, ar), Type::Fun(bp, br)) => {
            ap.len() == bp.len()
                && ap.iter().zip(bp).all(|(a, b)| sum_view_layouts_agree(a, b))
                && sum_view_layouts_agree(ar, br)
        }
        (Type::Tuple(a), Type::Tuple(b)) => {
            a.len() == b.len() && a.iter().zip(b).all(|(a, b)| sum_view_layouts_agree(a, b))
        }
        (Type::Record(a), Type::Record(b)) | (Type::Sum(a), Type::Sum(b)) => {
            a.id == b.id
                && (a.id >= 0 || a.name == b.name)
                && (a.id != brass_hir::STRUCTURAL_RECORD_ID
                    || a.substitution
                        .iter()
                        .map(|(k, _)| k)
                        .eq(b.substitution.iter().map(|(k, _)| k)))
                && a.substitution.iter().all(|(key, a)| {
                    b.substitution
                        .get(key)
                        .is_none_or(|b| sum_view_layouts_agree(a, b))
                })
        }
        _ => a == b,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sum_view(ok: Type, err: Type) -> Type {
        let mut n = NominalType::new(3, "Result");
        n.substitution.insert("Ok.value", ok);
        n.substitution.insert("Err.error", err);
        Type::Sum(n)
    }

    /// Fresh open payloads are compatible, but retained observations must
    /// expose a disagreement when those payloads resolve later.
    #[test]
    fn sum_view_observations_resolve_before_comparison() {
        let program = Program::empty();
        let mut checker =
            Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
        let a = checker.fresh_unknown();
        let b = checker.fresh_unknown();
        let err_a = checker.fresh_unknown();
        let err_b = checker.fresh_unknown();
        let span = Span::new(0, 1);
        checker.note_sum_view(span, Some(&sum_view(a.clone(), err_a)));
        checker.note_sum_view(span, Some(&sum_view(b.clone(), err_b)));
        assert!(checker.errors.is_empty());
        checker.solver.unify(&a, &Type::Int(IntKind::I32)).unwrap();
        checker.solver.unify(&b, &Type::Str).unwrap();
        checker.settle_sum_views();
        assert_eq!(checker.errors.len(), 1);
        assert!(
            checker.errors[0]
                .message
                .contains("different parent sum instantiations")
        );
    }

    /// Incomplete nominal observations do not poison a typeof annotation;
    /// a resolved nominal can subsequently provide its concrete type.
    #[test]
    fn typeof_waits_for_nested_nominal_substitutions() {
        let program = Program::empty();
        let mut checker =
            Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
        let open = checker.fresh_unknown();
        let mut record = NominalType::new(4, "Box");
        record.substitution.insert("item", open.clone());
        let ty = sum_view(Type::Record(record), Type::Void);
        let span = Span::new(0, 1);
        checker.record_typeof_type(span, &ty);
        assert!(!checker.typeof_types.contains_key(&span));
        checker
            .solver
            .unify(&open, &Type::Int(IntKind::I64))
            .unwrap();
        checker.record_typeof_type(span, &ty);
        assert_eq!(checker.typeof_types.get(&span), Some(&checker.resolve(&ty)));
        assert!(!checker.typeof_poisoned.contains(&span));
    }

    #[test]
    fn failed_composite_element_unification_rolls_back_earlier_bindings() {
        let program = Program::empty();
        let mut checker =
            Checker::new(&program, Rc::new(brass_typesys::RowInfo::analyze(&program)));
        let open = checker.fresh_unknown();
        let elem = Type::Tuple(vec![open.clone(), Type::Bool]);
        let got = Type::Tuple(vec![Type::Str, Type::Int(IntKind::I32)]);
        let expr = Expr::Null(Span::new(0, 1));

        checker.expect_element_assignable(&got, &elem, &expr);

        // Tuple unification binds the first component before the second fails;
        // suppressing that failure must not leave the first binding behind.
        assert!(checker.resolve(&open).is_unknown());
    }
}
