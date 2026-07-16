//! Assignability checks and operator typing: the `expect_*_assignable`
//! family (including integer-literal fitting and nullable widening)
//! and unary/binary operator type rules with their error rendering.

use super::*;

impl<'a> Checker<'a> {
    pub(super) fn check_unary(
        &mut self,
        op: UnaryOp,
        ty: &Type,
        span: prepoly_parser::Span,
    ) -> Type {
        match self.resolve(ty) {
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
                        unary_op_str(op),
                        other.display()
                    ),
                    span,
                });
                self.fresh_unknown()
            }
        }
    }

    pub(super) fn check_binary(
        &mut self,
        op: BinOp,
        left: &Type,
        right: &Type,
        span: prepoly_parser::Span,
    ) -> Type {
        self.check_binary_core(op, None, left, None, right, span)
    }

    pub(super) fn check_binary_expr(
        &mut self,
        op: BinOp,
        left_expr: &Expr,
        left: &Type,
        right_expr: &Expr,
        right: &Type,
        span: prepoly_parser::Span,
    ) -> Type {
        self.check_binary_core(op, Some(left_expr), left, Some(right_expr), right, span)
    }

    fn check_binary_core(
        &mut self,
        op: BinOp,
        left_expr: Option<&Expr>,
        left: &Type,
        right_expr: Option<&Expr>,
        right: &Type,
        span: prepoly_parser::Span,
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
        self.record_binary_shape(op, &left, &right);
        if let Some(ty) = integer_literal_binary_type(op, left_expr, &left, right_expr, &right) {
            return ty;
        }
        // Numeric arithmetic/comparison between mixed types implicitly converts
        // both operands to their common type.
        let is_unknown = matches!(left, Type::Unknown(_)) || matches!(right, Type::Unknown(_));
        let numeric_common = common_numeric_type(&left, &right);
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
                } else if let Some(t) = numeric_common {
                    t
                } else {
                    self.binary_error(op, &left, &right, span)
                }
            }
            // Remainder is integer-only (the widths may still differ).
            BinOp::Rem => {
                if is_unknown {
                    self.fresh_unknown()
                } else if let Some(t @ Type::Int(_)) = numeric_common {
                    t
                } else {
                    self.binary_error(op, &left, &right, span)
                }
            }
            BinOp::Eq | BinOp::Ne => {
                if numeric_common.is_some()
                    || self.can_unify(&left, &right)
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
                if numeric_common.is_some() || is_unknown {
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
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
                match (&left, &right) {
                    (Type::Int(a), Type::Int(b)) if a == b => left,
                    (Type::Unknown(_), _) | (_, Type::Unknown(_)) => self.fresh_unknown(),
                    _ => self.binary_error(op, &left, &right, span),
                }
            }
        }
    }

    fn binary_error(
        &mut self,
        op: BinOp,
        left: &Type,
        right: &Type,
        span: prepoly_parser::Span,
    ) -> Type {
        self.errors.push(TypeError {
            message: format!(
                "operator `{}` is not defined for `{}` and `{}` (no applicable conversion)",
                op_str(op),
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
    pub(super) fn record_sum_view(&mut self, got: &Type, want: &Type, span: prepoly_parser::Span) {
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
        self.sum_views.insert(span, resolved);
    }

    pub(super) fn expect_expr_assignable(&mut self, got: &Type, want: &Type, expr: &Expr) {
        if integer_literal_fits(expr, want) {
            return;
        }
        if float_literal_fits(expr, want) {
            return;
        }
        self.expect_assignable(got, want, expr.span());
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

    pub(super) fn expect_assignable(
        &mut self,
        got: &Type,
        want: &Type,
        span: prepoly_parser::Span,
    ) {
        let got = self.resolve(got);
        let want = self.resolve(want);
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
                Some(InferenceVarKind::ErrorOnlyOk) => {
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
        if got.is_null() && !matches!(want, Type::Nullable(_)) {
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
        if matches!(got, Type::Nullable(_))
            && !matches!(want, Type::Nullable(_))
            && !want.is_unknown()
        {
            self.report_nullable_use(span);
            return;
        }
        // A declared sum subtype flowing into its parent must be RECORDED so
        // MIR rebuilds the value -- `can_unify`'s structural fallback would
        // otherwise accept it silently and the unboxed layout would be
        // misread. Checked before the general acceptance paths, against the
        // nullable-stripped requirement (`Result<..>?` still coerces the sum).
        {
            let want_inner = match &want {
                Type::Nullable(inner) => inner.as_ref().clone(),
                other => other.clone(),
            };
            if let (Type::Sum(h), Type::Sum(w)) = (&got, &want_inner)
                && h.id != w.id
                && crate::structural::types_compatible(self.program, &got, &want_inner)
            {
                self.record_sum_view(&got, &want_inner, span);
                return;
            }
        }
        if let Type::Nullable(inner) = &want
            && (self.can_unify(&got, inner)
                || numeric_flows_into(&got, &self.resolve(inner))
                || matches!(got, Type::Never))
        {
            return;
        }
        if self.can_unify(&got, &want)
            || crate::structural::types_compatible(self.program, &got, &want)
        {
            return;
        }
        // Automatic numeric conversion: a numeric value flows into a numeric
        // position of another type (int widths/signedness, int -> float); the
        // back ends convert at the flow point. float -> int stays explicit.
        if numeric_flows_into(&got, &want) {
            return;
        }
        // A numeric pair that is not value-preserving gets the dedicated
        // narrowing diagnostic with the explicit-conversion hint from the
        // flow authority.
        if let prepoly_typesys::Flow::Forbidden(hint) = prepoly_typesys::numeric_flow(&got, &want)
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
        let (got, want) = prepoly_hir::mismatch_display(&got, &want);
        self.errors.push(TypeError {
            message: format!("cannot use `{got}` where `{want}` is required"),
            span,
        });
    }

    /// Check a value pushed/inserted into a slice against its element type. Unlike
    /// the bidirectional `expect_assignable` (whose reverse structural check the
    /// per-call hm pass re-gates for ordinary flow positions, but not for slice
    /// methods), this is one-directional: the value must be usable *as* the
    /// element, so a structural supertype is rejected and cannot corrupt the
    /// unboxed element layout. When the element type is still an open inference
    /// variable it is pinned to the value through `solver.unify`, so the occurs
    /// check fires -- pushing an array into itself (`a.push(a)`) is reported here
    /// instead of leaving the element unbound to be mistyped at the call site.
    pub(super) fn expect_element_assignable(&mut self, got: &Type, elem: &Type, expr: &Expr) {
        let got = self.resolve(got);
        let want = self.resolve(elem);
        if integer_literal_fits(expr, &want) {
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
            let outcome = match &want {
                Type::Nullable(inner) if !got.is_null() && !matches!(got, Type::Nullable(_)) => {
                    self.solver.unify(inner, &got)
                }
                _ => self.solver.unify(elem, &got),
            };
            if outcome.is_err() && want.is_unknown() {
                // The only hard failure on a *bare* element variable is the occurs
                // check: pushing the array into itself, an infinite element type.
                self.errors.push(TypeError {
                    message: "cannot push a value whose type contains this array; \
                              the element type would be infinite"
                        .to_string(),
                    span: expr.span(),
                });
            }
            // A failure against a *partially* fixed element (a record/array with
            // open components) is left to defer rather than reported: the store may
            // go through a witness alias the body itself re-reads (the table's
            // `_grow` re-inserts `old_entries[0]`), which is loose by construction.
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
        self.report_element_mismatch(&got, &want, expr.span());
    }

    /// Assignability into array-element storage. Elements are read back at the
    /// array's element type AND overwritten through it, so the position is
    /// invariant: a structural *width* supertype (a record with extra fields,
    /// hence a different layout) must not be stored where the narrower element
    /// type is expected -- reading it back would reinterpret the wider layout.
    /// One-directional `types_compatible` is only sound for consumed positions
    /// (arguments), not for shared mutable storage.
    fn element_assignable_into(&self, got: &Type, want: &Type) -> bool {
        Subst::new().unify(got, want).is_ok()
            || crate::structural::types_invariant(self.program, got, want)
    }

    fn report_element_mismatch(&mut self, got: &Type, want: &Type, span: prepoly_parser::Span) {
        let (got, want) = prepoly_hir::mismatch_display(got, want);
        self.errors.push(TypeError {
            message: format!("cannot use `{got}` where `{want}` is required"),
            span,
        });
    }
}

pub(super) fn integer_literal_fits(expr: &Expr, want: &Type) -> bool {
    // See through a nullable cell and the reference/mutability wrappers: assigning
    // an integer literal to a `ref(mut(int32))` element (an array index through a
    // mutable reference) targets the underlying `int32`.
    fn int_kind(t: &Type) -> Option<IntKind> {
        match t {
            Type::Int(kind) => Some(*kind),
            Type::Nullable(inner) | Type::Ref(inner) | Type::Mut(inner) | Type::ConstOf(inner) => {
                int_kind(inner)
            }
            _ => None,
        }
    }
    match (literal_int_value(expr), int_kind(want)) {
        (Some(value), Some(kind)) => int_fits_kind(value, kind),
        _ => false,
    }
}

/// The compile-time value of an integer literal expression, INCLUDING the
/// negated form: `-128` parses as `Unary(Neg, Int(128))`, and without this the
/// fit-based literal adaptation (`let m: int8 = -128`) would fall through to
/// the numeric-flow rules and be rejected as a narrowing.
pub(super) fn literal_int_value(expr: &Expr) -> Option<i64> {
    match expr {
        Expr::Int(v, _) => Some(*v),
        Expr::Unary(UnaryOp::Neg, inner, _) => match &**inner {
            // The lexer bounds a literal's magnitude to i64::MAX, so the
            // negation cannot overflow.
            Expr::Int(v, _) => Some(-*v),
            _ => None,
        },
        _ => None,
    }
}

/// Whether `expr` is a float LITERAL flowing into a float position. A literal
/// is the value the programmer wrote against that annotation, so it adapts to
/// any float width (the store converts) even though a float64 VALUE no longer
/// narrows implicitly.
pub(super) fn float_literal_fits(expr: &Expr, want: &Type) -> bool {
    fn is_float(t: &Type) -> bool {
        match t {
            Type::Float(_) => true,
            Type::Nullable(inner) | Type::Ref(inner) | Type::Mut(inner) | Type::ConstOf(inner) => {
                is_float(inner)
            }
            _ => false,
        }
    }
    let literal = matches!(expr, Expr::Float(..))
        || matches!(expr, Expr::Unary(UnaryOp::Neg, inner, _) if matches!(**inner, Expr::Float(..)));
    literal && is_float(want)
}

fn integer_literal_binary_type(
    op: BinOp,
    left_expr: Option<&Expr>,
    left: &Type,
    right_expr: Option<&Expr>,
    right: &Type,
) -> Option<Type> {
    if left_expr.is_some_and(|expr| integer_literal_fits(expr, right)) {
        return integer_literal_binary_result(op, right);
    }
    if right_expr.is_some_and(|expr| integer_literal_fits(expr, left)) {
        return integer_literal_binary_result(op, left);
    }
    None
}

fn integer_literal_binary_result(op: BinOp, contextual_type: &Type) -> Option<Type> {
    if !matches!(contextual_type, Type::Int(_)) {
        return None;
    }
    match op {
        BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::Div
        | BinOp::Rem
        | BinOp::BitAnd
        | BinOp::BitOr
        | BinOp::BitXor
        | BinOp::Shl
        | BinOp::Shr => Some(contextual_type.clone()),
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => Some(Type::Bool),
        BinOp::And | BinOp::Or => None,
    }
}

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

fn op_str(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Gt => ">",
        BinOp::Le => "<=",
        BinOp::Ge => ">=",
        BinOp::And => "&&",
        BinOp::Or => "||",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::BitXor => "^",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
    }
}

fn unary_op_str(op: UnaryOp) -> &'static str {
    match op {
        UnaryOp::Neg => "-",
        UnaryOp::Not => "!",
        UnaryOp::BitNot => "~",
    }
}
