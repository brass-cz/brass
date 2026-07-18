//! Shared typing rules of the monomorphizer: literal/operand typing,
//! the supported-type subset the typed back end accepts, nominal
//! resolution, binary-operator checking, and return-type merging.

use super::*;

/// The default concrete type of a constant literal (integers default to int32,
/// floats to float64). Errors on non-scalar constants.
pub(super) fn const_type(lit: &brass_mir::Literal) -> Result<Type, String> {
    use brass_mir::Literal;
    match lit {
        // An integer literal defaults by magnitude: int32 when it fits, int64
        // otherwise (a 64-bit constant like INT64_MAX must not truncate).
        Literal::Int(v) => Ok(Type::Int(int_literal_kind(*v))),
        Literal::Float(_) => Ok(Type::Float(FloatKind::F64)),
        Literal::Bool(_) => Ok(Type::Bool),
        Literal::Void => Ok(Type::Void),
        Literal::Str(_) => Ok(Type::Str),
        // The null literal: a nullable whose element type is unconstrained here
        // (it unifies with the contextual `T?` it is coerced to).
        Literal::Null => Ok(Type::Nullable(Box::new(Type::Never))),
    }
}

/// Whether a type is in the typed back end's scope: scalars, and records whose
/// fields are all supported (a fully-resolved field-type substitution).
pub(super) fn is_supported(ty: &Type) -> bool {
    is_supported_rec(ty, &mut HashSet::default())
}

/// `is_supported` with a guard against self-referential record types (e.g.
/// `type Node = { next: Node? }`): a nominal already on the visiting path is assumed
/// supported, so the check terminates. A recursive field is a heap pointer, so the
/// layout is finite even though the type definition is cyclic.
/// Fill a record's field-type substitution from its HIR declaration when it is a
/// bare reference (empty substitution -- a sum variant field's declared type once
/// bound, or a nested declared field). The resolved record is self-describing, so
/// `is_supported` and field-access inference treat it like a constructed value
/// without relaxing the support check for genuinely-unresolved types. Recurses into
/// field and wrapper types; a record already being resolved (a cycle such as
/// `Node { next: Node? }`) is left bare and handled by `is_supported_rec`'s visiting
/// guard. A sum carries no value substitution (its layout comes from the HIR), so it
/// is already self-describing and left as is.
pub(super) fn resolve_nominal(program: &Program, ty: &Type) -> Type {
    fn go(program: &Program, ty: &Type, stack: &mut HashSet<i32>) -> Type {
        match ty {
            Type::Record(n) if n.substitution.is_empty() => {
                let Some(info) = program.type_by_id(n.id) else {
                    return ty.clone();
                };
                let TypeKind::Record { fields, .. } = &info.kind else {
                    return ty.clone();
                };
                if !stack.insert(n.id) {
                    return ty.clone(); // already resolving this type: a cycle
                }
                let mut subst = Substitution::empty();
                for f in fields {
                    if let Some(t) = &f.resolved_ty {
                        subst.insert(f.name.clone(), go(program, t, stack));
                    }
                }
                stack.remove(&n.id);
                Type::Record(NominalType::with_substitution(n.id, n.name.clone(), subst))
            }
            // An already-substituted record may still carry bare references in
            // its entries (a declared field's nominal type, e.g. the seed of an
            // uninitialized `let`); resolve them in place.
            Type::Record(n) => {
                if !stack.insert(n.id) {
                    return ty.clone();
                }
                let mut subst = Substitution::empty();
                for (k, v) in n.substitution.iter() {
                    subst.insert(k.to_string(), go(program, v, stack));
                }
                stack.remove(&n.id);
                Type::Record(NominalType::with_substitution(n.id, n.name.clone(), subst))
            }
            Type::Nullable(inner) => Type::Nullable(Box::new(go(program, inner, stack))),
            Type::Slice(inner) => Type::Slice(Box::new(go(program, inner, stack))),
            Type::Array(inner, k) => Type::Array(Box::new(go(program, inner, stack)), *k),
            _ => ty.clone(),
        }
    }
    go(program, ty, &mut HashSet::default())
}

/// Whether a sum variant's field can be laid out by the typed back end. An
/// unannotated field with no inferred type (`None`/`Unknown`) is allowed as long
/// as it is never accessed: it occupies an opaque, pointer-sized slot. Any other
/// field type must be concretely supported once its nominal references are resolved
/// (a record/sum field is a heap pointer whose own layout is monomorphized
/// independently).
pub(super) fn variant_field_layoutable(program: &Program, ty: &Option<Type>) -> bool {
    match ty {
        None | Some(Type::Unknown(_)) => true,
        Some(t) => is_supported(&resolve_nominal(program, t)),
    }
}

fn is_supported_rec(ty: &Type, visiting: &mut HashSet<i32>) -> bool {
    match ty {
        Type::Bool | Type::Int(_) | Type::Float(_) | Type::Void | Type::Str => true,
        // `Never` only types values on a statically-unreachable path -- e.g. the
        // truthy arm of `if x` for a bare `null` (`never?`), where narrowing
        // yields `never`. The arm is type-checked (so payloads still infer) but
        // the back end skips emitting it, so an opaque placeholder slot suffices.
        Type::Never => true,
        Type::Record(n) => {
            if !visiting.insert(n.id) {
                return true; // already on the path: a self-reference, finite layout
            }
            // A bare reference (empty substitution -- a field's declared nominal
            // type, or a sum variant binding) is a supported heap pointer; its own
            // field concreteness is validated when the record is monomorphized as a
            // value. A fieldless record (`type Empty = {}`) also lands here: its
            // substitution is empty even when constructed, and an empty layout is
            // trivially supported. A substituted (constructed/generic) record
            // additionally requires every field type to be supported. This mirrors
            // how a `Sum` is trusted as a pointer below.
            let ok = n.substitution.is_empty()
                || n.substitution
                    .iter()
                    .all(|(_, t)| is_supported_rec(t, visiting));
            visiting.remove(&n.id);
            ok
        }
        // A bare sum reference (empty substitution) is a supported heap pointer
        // whose per-variant field concreteness is checked at construction
        // (`variant_type`). A substituted sum -- a constructed `Result<T, E>` --
        // additionally requires its payload types to be supported, so an open `T!`
        // error payload (an unresolved `Unknown`) is rejected here. That makes a
        // `-> T!` signature's annotation unsupported, so `instantiate_fn` drops it
        // and the engine infers the concrete `Result` from the body instead.
        Type::Sum(n) => {
            if !visiting.insert(n.id) {
                return true; // already on the path: a self-reference, finite layout
            }
            let ok = n.substitution.is_empty()
                || n.substitution
                    .iter()
                    .all(|(_, t)| is_supported_rec(t, visiting));
            visiting.remove(&n.id);
            ok
        }
        Type::Slice(elem) | Type::Array(elem, _) => is_supported_rec(elem, visiting),
        // A tuple is a fixed heterogeneous aggregate; supported when every element is.
        Type::Tuple(elems) => elems.iter().all(|t| is_supported_rec(t, visiting)),
        // A closure value (a typed environment + function pointer).
        Type::Fun(params, ret) => {
            params.iter().all(|p| is_supported_rec(p, visiting)) && is_supported_rec(ret, visiting)
        }
        // A nullable value (a heap cell pointer, null = null pointer). `Never` is
        // the element type of the bare `null` literal until it is coerced.
        Type::Nullable(inner) => {
            matches!(**inner, Type::Never) || is_supported_rec(inner, visiting)
        }
        _ => false,
    }
}

/// Check that a binary operator's operands have compatible, in-scope types.
pub(super) fn check_bin(op: BinOp, a: &Type, b: &Type) -> Result<(), String> {
    // `x == null` / `x != null` (or comparing nullables) is a null/identity test.
    if matches!(op, BinOp::Eq | BinOp::Ne)
        && (matches!(a, Type::Nullable(_)) || matches!(b, Type::Nullable(_)))
    {
        return Ok(());
    }
    // A nullable operand in an arithmetic/comparison context is narrowed to its
    // element type (valid programs guard for null first); the back end unwraps it.
    let a = unwrap_nullable(a);
    let b = unwrap_nullable(b);
    // `never` is the bottom type: it only reaches here on a statically-dead path
    // (a bare `null` narrowed in an always-false `if` arm), which the back end
    // never emits, so any operator over it is vacuously well-typed.
    if matches!(a, Type::Never) || matches!(b, Type::Never) {
        return Ok(());
    }
    let same = a == b;
    let integer = |t: &Type| matches!(t, Type::Int(_));
    let both_int = integer(a) && integer(b);
    match op {
        // `+` is numeric addition or string concatenation. Two integers may
        // differ in width (a literal adapts to the other's type; the back end
        // coerces both to the operand type).
        // Numeric operands of differing types implicitly convert to their common
        // type (mixed width, signedness, and int-with-float); `+` also concatenates
        // two strings.
        BinOp::Add => {
            if brass_typesys::common_numeric_type(a, b).is_some()
                || (same && matches!(a, Type::Str))
            {
                Ok(())
            } else {
                Err(format!(
                    "`Add` needs two numeric/string operands, got {} and {}",
                    a.display(),
                    b.display()
                ))
            }
        }
        BinOp::Sub | BinOp::Mul | BinOp::Div => {
            if brass_typesys::common_numeric_type(a, b).is_some() {
                Ok(())
            } else {
                Err(format!(
                    "`{op:?}` needs two numeric operands, got {} and {}",
                    a.display(),
                    b.display()
                ))
            }
        }
        // Remainder is integer-only but the widths may differ (coerced to the
        // common int); the bitwise/shift operators need two equal integers.
        BinOp::Rem => {
            if both_int {
                Ok(())
            } else {
                Err(format!(
                    "`Rem` needs two integer operands, got {} and {}",
                    a.display(),
                    b.display()
                ))
            }
        }
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
            if same && integer(a) {
                Ok(())
            } else {
                Err(format!(
                    "`{op:?}` needs two equal integer operands, got {} and {}",
                    a.display(),
                    b.display()
                ))
            }
        }
        // A numeric comparison converts mixed operands to a common type; equality
        // also applies to two bools or two strings.
        BinOp::Eq | BinOp::Ne => {
            if brass_typesys::common_numeric_type(a, b).is_some()
                || (same && matches!(a, Type::Bool | Type::Str))
            {
                Ok(())
            } else {
                Err(format!(
                    "`{op:?}` needs two comparable operands, got {} and {}",
                    a.display(),
                    b.display()
                ))
            }
        }
        BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
            if brass_typesys::common_numeric_type(a, b).is_some() {
                Ok(())
            } else {
                Err(format!(
                    "`{op:?}` needs two comparable numeric operands, got {} and {}",
                    a.display(),
                    b.display()
                ))
            }
        }
        BinOp::And | BinOp::Or => Err(format!("`{op:?}` is unsupported on the typed backend")),
    }
}

/// Shared operand-type rule used by both the typer and the typed dispatch to
/// pick a binary op's operand type: for two integers of different widths, the
/// wider (so a narrower operand is coerced up); otherwise a `Local` operand's
/// type, preferring a non-constant.
pub fn binary_operand_type(a: &Operand, b: &Operand, local_types: &[Type]) -> Type {
    let ra = operand_type_of(a, local_types);
    let rb = operand_type_of(b, local_types);
    // A comparison against the null literal keeps the nullable type (the back end
    // compares pointers); other nullables narrow to their element type.
    let null_lit = |t: &Type| matches!(t, Type::Nullable(inner) if matches!(**inner, Type::Never));
    if null_lit(&ra) {
        return rb;
    }
    if null_lit(&rb) {
        return ra;
    }
    binary_operand_common(
        &ra,
        &rb,
        matches!(a, Operand::Local(_)),
        matches!(b, Operand::Local(_)),
    )
}

/// The one operand-type rule shared by the typer (`Monomorphizer::
/// binary_operand_type`) and the back ends' comparison-operand pick
/// ([`binary_operand_type`]), given both resolved operand types. Nullables
/// narrow to their element type (a guarded `int32?` compares as `int32`). An
/// integer literal adapts to the variable operand's int kind (`byte - 32`
/// stays uint8) -- but only when its magnitude-derived kind fits that kind's
/// width. A wider literal (`uint8 < 300`) must not truncate, so the operands
/// take their common (wider) numeric type instead, matching the checker's
/// numeric-flow rules.
pub(super) fn binary_operand_common(ta: &Type, tb: &Type, a_local: bool, b_local: bool) -> Type {
    let na = unwrap_nullable(ta);
    let nb = unwrap_nullable(tb);
    if let (Type::Int(ka), Type::Int(kb)) = (na, nb)
        && a_local != b_local
    {
        let (lit, var) = if a_local { (kb, ka) } else { (ka, kb) };
        if lit.bits() <= var.bits() {
            return Type::Int(*var);
        }
    }
    // Mixed numeric operands implicitly convert to their common type (wider
    // width, signedness, and int-with-float).
    if let Some(common) = brass_typesys::common_numeric_type(na, nb) {
        return common;
    }
    if a_local || !b_local {
        na.clone()
    } else {
        nb.clone()
    }
}

/// The operand-type pair `validate` should check for a binary statement: a
/// const integer literal takes the kind it adapts to at codegen (the first
/// clause of [`binary_operand_common`]), so validation sees the pair the back
/// ends actually emit -- `u64_counter + 1` is uint64/uint64, not the
/// literal's magnitude-default uint64/int32. Every other pair validates at
/// its own types.
pub(super) fn bin_validation_types(
    ta: &Type,
    tb: &Type,
    a_local: bool,
    b_local: bool,
) -> (Type, Type) {
    if let (Type::Int(ka), Type::Int(kb)) = (unwrap_nullable(ta), unwrap_nullable(tb))
        && a_local != b_local
    {
        let (lit, var) = if a_local { (kb, ka) } else { (ka, kb) };
        if lit.bits() <= var.bits() {
            return (Type::Int(*var), Type::Int(*var));
        }
    }
    (ta.clone(), tb.clone())
}

/// Scan a body for `arr.push(elem)` calls, mapping each array local (resolved
/// through `Use` aliases) to a pushed element operand. Used to infer the element
/// Join two return-operand types of an unannotated non-fallible callable. The
/// front end has already checked the returns are mutually consistent, so this only
/// reconciles the nullable/never lattice: a `return null` path (`never?`) combined
/// with a value-returning path yields that value's nullable type, and an
/// unreachable `Never` arm is absorbed by the other. Without this join the inferred
/// return type would be whichever return block the fixpoint typed first, so a `get`
/// returning `value` or `null` could freeze to the bare `value` type and then have
/// its `null` path rejected as "returns a null value where `T` is required".
pub(super) fn merge_return_types(a: &Type, b: &Type) -> Type {
    fn nullable_of(t: Type) -> Type {
        match t {
            Type::Nullable(_) => t,
            other => Type::Nullable(Box::new(other)),
        }
    }
    match (a, b) {
        _ if a == b => a.clone(),
        // `Never` types only a statically-unreachable path; the other arm wins.
        (Type::Never, _) => b.clone(),
        (_, Type::Never) => a.clone(),
        // A bare `null` return joining a void fall-through (a nullable `!`
        // used as a statement): the callable is void -- the null carries no
        // value a caller could observe, and a `void?` return would give the
        // fall-through path no representable value.
        (Type::Nullable(x), Type::Void) | (Type::Void, Type::Nullable(x))
            if matches!(**x, Type::Never) =>
        {
            Type::Void
        }
        (Type::Nullable(x), Type::Nullable(y)) => {
            Type::Nullable(Box::new(merge_return_types(x, y)))
        }
        // One nullable and one bare value (commonly `never?` from `null` vs a real
        // value): the result is nullable over the joined element type.
        (Type::Nullable(x), y) => nullable_of(merge_return_types(x, y)),
        (x, Type::Nullable(y)) => nullable_of(merge_return_types(x, y)),
        // Two distinct non-null types should not occur in a checked program; keep
        // the first so inference stays deterministic rather than panicking.
        _ => a.clone(),
    }
}

/// Whether `specific` is `general` with equal-or-more payload information:
/// the same shape through nullables, the same nominal, and every
/// record-field/variant-payload slot `general` pins present in `specific`
/// with a matching (or further-refined) type. A bare nominal return
/// annotation relates to the body's inferred instance exactly this way, so
/// the inferred side may stand in for the annotation without loosening the
/// contract the annotation states.
pub(super) fn is_refinement_of(general: &Type, specific: &Type) -> bool {
    match (general, specific) {
        // An open slot (a declaration's shared inference variable carried
        // into a bare instance) is information-free: anything refines it.
        (Type::Unknown(_), _) => true,
        (Type::Nullable(g), Type::Nullable(s)) => is_refinement_of(g, s),
        (Type::Record(g), Type::Record(s)) | (Type::Sum(g), Type::Sum(s)) => {
            g.id == s.id
                && (g.id >= 0 || g.name() == s.name())
                && g.substitution.iter().all(|(k, gt)| {
                    s.substitution
                        .get(k)
                        .is_some_and(|st| is_refinement_of(gt, st))
                })
        }
        _ => general == specific,
    }
}

/// Strip one level of nullable: the inner type of a `T?`, else `ty` unchanged.
/// Used to narrow a value proven non-null by a guard (`if a`) -- the MIR local
/// still carries the declared nullable -- in arithmetic/comparison and as the
/// receiver of an aggregate operation (field/element/`len`/`push`/...).
pub fn unwrap_nullable(ty: &Type) -> &Type {
    match ty {
        Type::Nullable(inner) => inner,
        other => other,
    }
}
