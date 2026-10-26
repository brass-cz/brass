//! Typing of the conversion calls on a type word: the primitive
//! `T.from`/`T.parse` conversions with their argument constraints, the
//! rendering `string.from`, which record types have the builtin structural
//! `T.from` (a type's declared static `from` shadows it), and the source literal
//! offered to that conversion.

use super::*;

impl<'a> Checker<'a> {
    /// The record a structural conversion `T.from(v)` builds, as the type
    /// `T` denotes and its fields: a declared record, or a `type A = R { .. }`
    /// alias of one -- its instance, whose pinned fields carry the pinned
    /// types (so the conversion fills `A`'s pinned slots). `None` when `T`
    /// names no record, or a record that declares a static `from`
    /// (`TypeInfo::has_structural_from`): the declared `from` shadows the
    /// builtin conversion, and the call reaches it like any static method.
    pub(super) fn conversion_target(
        &mut self,
        qualifier: &str,
    ) -> Option<(Type, Vec<brass_hir::FieldInfo>)> {
        if let Some(info) = self.program.resolve_type(&self.current_module, qualifier) {
            return match &info.kind {
                TypeKind::Record { fields, .. } if info.has_structural_from() => {
                    Some((info.type_ref(), fields.clone()))
                }
                _ => None,
            };
        }
        let Some(Type::Record(n)) = self.resolve_alias(qualifier) else {
            return None;
        };
        let info = self.program.type_by_id(n.id)?;
        let TypeKind::Record { fields, .. } = &info.kind else {
            return None;
        };
        if !info.has_structural_from() {
            return None;
        }
        let fields = fields
            .iter()
            .map(|f| {
                let mut f = f.clone();
                if let Some(pin) = n.substitution.get(&f.name) {
                    f.resolved_ty = Some(pin.clone());
                }
                f
            })
            .collect();
        Some((Type::Record(n), fields))
    }

    /// The anonymous record literal offered to `T.from({ .. })`. Each field
    /// written as a numeric literal flows into `T`'s field of that name like
    /// any literal flowing into a slot: it takes the field's numeric type when
    /// its value fits (`G.from({ x: 5 })` with `x: float32` converts), and
    /// keeps its default type otherwise, so the conversion answers `null`
    /// instead of narrowing. Every other field is typed on its own.
    pub(super) fn check_from_source_literal(
        &mut self,
        literal: &Expr,
        fields: &[(String, Expr)],
        target_fields: &[brass_hir::FieldInfo],
        scopes: &mut ScopeStack,
    ) -> Type {
        let typed: Vec<(String, Type)> = fields
            .iter()
            .map(|(fname, value)| {
                let slot = target_fields
                    .iter()
                    .find(|f| &f.name == fname)
                    .and_then(|f| f.resolved_ty.as_ref())
                    .map(|t| match t {
                        Type::Nullable(inner) => (**inner).clone(),
                        other => other.clone(),
                    })
                    .filter(|t| matches!(t, Type::Int(_) | Type::Float(_)));
                let adapted = slot.filter(|t| {
                    brass_typesys::NumericLiteral::of_expr(value).is_some_and(|lit| lit.fits(t))
                });
                let ty = match adapted {
                    Some(t) => {
                        self.record_expr_type(value, &t);
                        t
                    }
                    None => self.check_expr(value, scopes),
                };
                (fname.clone(), ty)
            })
            .collect();
        let ty = brass_hir::structural_record(typed);
        self.record_expr_type(literal, &ty);
        ty
    }

    /// Type a static call on a primitive type word (`int32.from`,
    /// `float64.parse`, `string.from`, `T.default()`), checking every
    /// argument; `None` when `tname.method` is no primitive static.
    pub(super) fn primitive_static_call(
        &mut self,
        tname: &str,
        method: &str,
        args: &[Arg],
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        let ret = self.primitive_static_type(tname, method)?;
        let arg_types: Vec<Type> = args
            .iter()
            .map(|a| self.check_expr(&a.expr, scopes))
            .collect();
        // `string.from(x)` renders like `"{x}"`: a declared `display` runs,
        // and a value with no rendering (a `void`, a function value) is
        // rejected.
        if (tname, method) == ("string", "from") {
            for (ty, arg) in arg_types.iter().zip(args) {
                self.expect_renderable(ty, arg.expr.span(), "`string.from` cannot render");
                self.invalidate_after_rendering(ty, scopes);
            }
        }
        self.check_numeric_conversion_args(tname, method, &arg_types, args);
        Some(ret)
    }

    /// Constrain the source type of the numeric conversions:
    /// `intN.from`/`floatN.from` take a numeric value and `intN.parse`/
    /// `floatN.parse` take a string, so `float64.from("abc")` is rejected
    /// rather than producing `0.0`. `string.from` takes any renderable value
    /// (see `primitive_static_call`). An argument still open here (a generic
    /// body's definitional pass) is judged by each instantiation's
    /// elaboration at its concrete type.
    fn check_numeric_conversion_args(
        &mut self,
        tname: &str,
        method: &str,
        arg_types: &[Type],
        args: &[Arg],
    ) {
        let numeric_target =
            IntKind::from_name(tname).is_some() || matches!(tname, "float32" | "float64");
        if !numeric_target {
            return;
        }
        let (Some(arg_ty), Some(arg)) = (arg_types.first(), args.first()) else {
            return;
        };
        // A `ref`/`mut`/`const` view converts like the value it views.
        let resolved = brass_hir::peel_modes(&self.resolve(arg_ty)).clone();
        if resolved.is_unknown() {
            return;
        }
        match method {
            "parse" if !matches!(resolved, Type::Str) => {
                self.errors.push(TypeError {
                    message: format!(
                        "`{tname}.parse` expects a string, found `{}`",
                        resolved.display()
                    ),
                    span: arg.expr.span(),
                });
            }
            "from" if !matches!(resolved, Type::Int(_) | Type::Float(_)) => {
                self.errors.push(TypeError {
                    message: format!(
                        "`{tname}.from` expects a numeric value, found `{}`",
                        resolved.display()
                    ),
                    span: arg.expr.span(),
                });
            }
            _ => {}
        }
    }
}
