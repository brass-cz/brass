//! Concrete-type queries shared by the walk, the compiling back ends, and
//! the interpreter: `Result` payload, field, element, index, and builtin
//! result types, how a record view or a `T.from` conversion fills each
//! field, and the payload of a constant string operand.

use super::*;

/// The `Ok` payload type of a `Result` return type (`void` if not a `Result`).
/// A `Result<..>?` return (a body that also propagates a null) reads as its
/// inner `Result`.
pub fn result_ok_type(ret: &Type) -> Type {
    match strip_ret_nullable(ret) {
        Type::Sum(n) => n
            .result_payloads()
            .map(|(ok, _)| ok.clone())
            .unwrap_or(Type::Void),
        _ => Type::Void,
    }
}

/// A fallible return type with its outer nullability stripped: `Result<..>?`
/// (a body that also propagates a null) reads as its `Result`.
pub(super) fn strip_ret_nullable(ret: &Type) -> &Type {
    match ret {
        Type::Nullable(inner) if inner.is_result_type() => inner,
        other => other,
    }
}

/// The concrete type of field `name` in a record type, or `void` if absent.
pub fn record_field_type(record_ty: &Type, name: &str) -> Type {
    match unwrap_nullable(record_ty) {
        Type::Record(n) => n.substitution.get(name).cloned().unwrap_or(Type::Void),
        _ => Type::Void,
    }
}

/// The concrete slot type of field `name` in an aggregate a field store writes
/// into: a record's substituted field type ([`record_field_type`]), or for a
/// sum the field's type in the first variant that declares it -- a bare name
/// is a field common to every variant (the checker only accepts such a store),
/// and a `Variant.field` key names one variant. `void` when the field is absent.
///
/// Both back ends type the stored operand with this, so the value is converted
/// to the slot's representation and the overwritten value is released at the
/// slot's type, for sum payload slots exactly as for record fields.
pub fn aggregate_field_type(program: &brass_hir::Program, base_ty: &Type, name: &str) -> Type {
    match unwrap_nullable(base_ty) {
        Type::Sum(n) => {
            let (want_variant, fname) = match name.split_once('.') {
                Some((v, f)) => (Some(v), f),
                None => (None, name),
            };
            let Some(brass_hir::TypeKind::Sum { variants }) =
                program.type_by_id(n.id).map(|info| &info.kind)
            else {
                return Type::Void;
            };
            variants
                .iter()
                .filter(|v| want_variant.is_none_or(|w| w == v.name))
                .find_map(|v| {
                    let (_, fields) = crate::render::render_variant_fields(program, n, &v.name)?;
                    fields
                        .into_iter()
                        .find_map(|(field, ty)| (field == fname).then_some(ty))
                })
                .unwrap_or(Type::Void)
        }
        _ => record_field_type(base_ty, name),
    }
}

/// The field names of a record type, in its substitution's (sorted) order.
pub fn record_field_names(record_ty: &Type) -> Vec<String> {
    match record_ty {
        Type::Record(n) => n
            .substitution
            .iter()
            .map(|(name, _)| name.to_string())
            .collect(),
        _ => Vec::new(),
    }
}

/// See through reference/mutability/const wrappers (erased before the back ends,
/// but peeled defensively) to the underlying type.
pub fn strip_wrappers(ty: &Type) -> &Type {
    match ty {
        Type::Ref(inner) | Type::Mut(inner) | Type::ConstOf(inner) => strip_wrappers(inner),
        other => other,
    }
}

/// How one field of a [`brass_mir::Rvalue::RecordView`] is materialized for a
/// concrete (per-instance) source type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ViewFieldPlan {
    /// Copy the source's field into the slot unchanged.
    Copy,
    /// The source lacks the (guarded) field, or carries it at a type the
    /// body cannot use: the view stores null.
    Null,
}

/// The per-field construction plan of a view: each field of `view_ty` (the
/// structural record the monomorphizer derived from the callee's row, see
/// [`brass_typesys::view_type`]) with its slot type and how the concrete
/// `src_ty` fills it. Derived purely from the two types, so the compiling back
/// ends and the interpreter make the identical decision the type derivation
/// made: a slot at the source field's own type copies it as is, and any other
/// slot -- the always-null `never?` of a guarded field the source lacks or
/// cannot supply -- stores null.
pub fn view_field_plans(view_ty: &Type, src_ty: &Type) -> Vec<(String, Type, ViewFieldPlan)> {
    let Type::Record(view) = view_ty else {
        return Vec::new();
    };
    let src = match strip_wrappers(src_ty) {
        Type::Record(n) => Some(n),
        _ => None,
    };
    view.substitution
        .iter()
        .map(|(name, fty)| {
            let same = src.and_then(|s| s.substitution.get(name)) == Some(fty);
            let plan = if same {
                ViewFieldPlan::Copy
            } else {
                ViewFieldPlan::Null
            };
            (name.to_string(), fty.clone(), plan)
        })
        .collect()
}

/// Whether `T.from(source)` succeeds for a concrete (per-instance) `src_ty` and
/// target record `target`: the source must be a record carrying every field
/// `target` declares, each holding a value that flows into the target field
/// ([`record_from_field_flows`]). Otherwise -- a missing field, or one whose
/// value does not flow -- the conversion yields null rather than reading a
/// field that is absent or of another type.
pub fn record_from_succeeds(src_ty: &Type, target: &Type) -> bool {
    let (Type::Record(s), Type::Record(t)) = (strip_wrappers(src_ty), target) else {
        return false;
    };
    t.substitution.iter().all(|(name, tty)| {
        s.substitution
            .get(name)
            .is_some_and(|sty| record_from_field_flows(sty, tty))
    })
}

/// Whether a `T.from(v)` source field of type `have` fills a target field of
/// type `want` by the language's flow conversions: the same type, a
/// value-preserving numeric widening, or a non-null value (widened likewise)
/// into a nullable field. A nullable source field fills a nullable target
/// field only of the same type, or always when the source is the bare `null`
/// (`never?`). Both back ends convert the read value to `want` with their
/// ordinary flow coercion.
pub fn record_from_field_flows(have: &Type, want: &Type) -> bool {
    let have = strip_wrappers(have);
    if have == want || brass_typesys::field_satisfies(have, want) {
        return true;
    }
    match (have, want) {
        (Type::Nullable(h), Type::Nullable(_)) => matches!(**h, Type::Never),
        (_, Type::Nullable(inner)) => brass_typesys::field_satisfies(have, inner),
        _ => false,
    }
}

/// The string payload of a constant string operand (the variant/panic argument
/// of a MIR-internal builtin call), if it is one.
pub fn str_const(op: &Operand) -> Option<&str> {
    match op {
        Operand::Const(Literal::Str(s)) => Some(s),
        _ => None,
    }
}

/// Typed return shapes for compiler/runtime builtins that are not backed by a
/// monomorphized function instance. Unknown shapes are left as `None`; callers
/// then assume the destination type already matches. Paired with
/// [`Codegen::codegen_builtin`], which emits these builtins: a builtin emitted
/// there needs an entry here exactly when its result shape can differ from its
/// destination (e.g. a nullable-returning primitive flowing into a narrowed
/// slot).
pub(super) fn builtin_result_type(
    name: &str,
    args: &[Operand],
    local_types: &[Type],
) -> Option<Type> {
    match name {
        "value_matches" | "result_is_ok" | "__nullable_context_present" => Some(Type::Bool),
        "__deep_copy" => args.first().map(|op| operand_type_of(op, local_types)),
        "__nonnull" => args
            .first()
            .map(|op| unwrap_nullable(&operand_type_of(op, local_types)).clone()),
        "panic" | "_panic" | "print" | "println" | "spawn" | "sync" | "_freeze" | "_cown" => {
            Some(Type::Void)
        }
        // The group-acquire wrap yields its closure's result, like `with`.
        "_with_all" => match args.first().map(|op| operand_type_of(op, local_types)) {
            Some(Type::Fun(_, ret)) => Some(*ret),
            _ => None,
        },
        "len" | "array_len" => Some(Type::Int(brass_hir::IntKind::I64)),
        "to_string" => Some(Type::Str),
        "_float_sqrt" | "_float_floor" | "_float_ceil" | "_float_pow" => {
            Some(Type::Float(brass_hir::FloatKind::F64))
        }
        "_string_slice" | "_string_concat" => Some(Type::Str),
        "_string_bytes" => Some(Type::Slice(Box::new(Type::Int(brass_hir::IntKind::U8)))),
        "_string_find" => Some(Type::Nullable(Box::new(Type::Int(brass_hir::IntKind::I64)))),
        "_string_char_at" => Some(Type::Nullable(Box::new(Type::Str))),
        "_string_cmp" => Some(Type::Int(brass_hir::IntKind::I32)),
        "_int_to_string" | "_float_to_string" => Some(Type::Str),
        "_int_to_float" => Some(Type::Float(brass_hir::FloatKind::F64)),
        // Native-plugin dispatch: the result shape is in the name's suffix.
        // Every other name has an arm above, so this decodes once and yields
        // `None` for a non-plugin builtin.
        n => brass_hir::plugin_builtin_return(n),
    }
}

/// The element type of an array/slice type, or `void` if not a sequence. A
/// narrowed nullable array (`int32[]?` proven non-null) is unwrapped first.
pub fn element_type(ty: &Type) -> Type {
    match unwrap_nullable(ty) {
        Type::Slice(e) | Type::Array(e, _) => (**e).clone(),
        _ => Type::Void,
    }
}

/// The concrete type of an index operand (the loop counter / index expression).
pub(super) fn index_type(idx: &Operand, f: &MonoFunction) -> Type {
    operand_type_of(idx, &f.local_types)
}
