//! Shared typing rules of the monomorphizer: literal/operand typing,
//! the supported-type subset the typed back end accepts, nominal
//! resolution, binary-operator checking, and the refinement relation between
//! instances of one nominal declaration.

use super::*;

/// The default concrete type of a constant literal: an integer by its value
/// (`brass_typesys::int_literal_kind`), a float `float64`.
pub(super) fn const_type(lit: &brass_mir::Literal) -> Result<Type, String> {
    use brass_mir::Literal;
    match lit {
        Literal::Int(v) => brass_typesys::int_literal_kind(*v)
            .map(Type::Int)
            .ok_or_else(|| {
                format!(
                    "internal error: integer literal {v} is out of range for every integer type"
                )
            }),
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
            Type::Tuple(elems) => {
                Type::Tuple(elems.iter().map(|e| go(program, e, stack)).collect())
            }
            Type::Fun(params, ret) => Type::Fun(
                params.iter().map(|p| go(program, p, stack)).collect(),
                Box::new(go(program, ret, stack)),
            ),
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

/// `is_supported` with a guard against self-referential record types (e.g.
/// `type Node = { next: Node? }`): a nominal already on the visiting path is assumed
/// supported, so the check terminates. A recursive field is a heap pointer, so the
/// layout is finite even though the type definition is cyclic.
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

/// The value of a numeric-literal operand (a MIR constant), which the
/// shared operator rule needs to decide whether the literal adapts to the
/// other operand.
pub(super) fn operand_literal(op: &Operand) -> Option<brass_typesys::NumericLiteral> {
    match op {
        Operand::Const(brass_mir::Literal::Int(v)) => Some(brass_typesys::NumericLiteral::Int(*v)),
        Operand::Const(brass_mir::Literal::Float(v)) => {
            Some(brass_typesys::NumericLiteral::Float(*v))
        }
        _ => None,
    }
}

/// Check that a binary operator's operands (each its monomorphized type and
/// operand) have compatible, in-scope types. Numeric pairs are decided by the
/// shared operator rule (`brass_typesys::numeric_binary`) -- the one the
/// checker typed the expression with -- so a checked program never fails
/// here on a numeric pair.
pub(super) fn check_bin(
    program: &Program,
    op: BinOp,
    (a, a_op): (&Type, &Operand),
    (b, b_op): (&Type, &Operand),
) -> Result<(), String> {
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
    let numeric = brass_typesys::numeric_binary(
        op,
        brass_typesys::NumericOperand::new(a, operand_literal(a_op)),
        brass_typesys::NumericOperand::new(b, operand_literal(b_op)),
    );
    let error = match numeric {
        Ok(_) => return Ok(()),
        Err(brass_typesys::OperatorError::NotNumeric) => None,
        Err(brass_typesys::OperatorError::NoCommonType) => Some("no common numeric type"),
        Err(brass_typesys::OperatorError::IntegerOnly) => Some("integer operands required"),
    };
    let same = a == b;
    let accepted = match op {
        // `+` also concatenates two strings.
        BinOp::Add => same && matches!(a, Type::Str),
        // Equality also applies to two operands of one type -- bools,
        // strings, records, sums, arrays, tuples, function values -- compared
        // structurally by the shared definition in `crate::equality`.
        BinOp::Eq | BinOp::Ne => crate::equality::equality_defined(program, a, b),
        BinOp::And | BinOp::Or => {
            return Err(format!(
                "internal error: `{op:?}` is unsupported on the typed backend"
            ));
        }
        _ => false,
    };
    if accepted && error.is_none() {
        return Ok(());
    }
    Err(format!(
        "internal error: `{op:?}` is not defined for {} and {}{}",
        a.display(),
        b.display(),
        error.map(|e| format!(" ({e})")).unwrap_or_default()
    ))
}

/// Whether a binary operator is a comparison (its result is `bool`, whatever
/// its operand types are). Shared by the monomorphizer and the back ends.
pub fn is_comparison(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge
    )
}

/// The type a binary operator's operands are converted to, shared by the
/// typer and the back ends (which compute a comparison at it). A comparison
/// against the null literal keeps the nullable type (the back end compares
/// pointers); otherwise `binary_operand_common` decides.
pub fn binary_operand_type(a: &Operand, b: &Operand, local_types: &[Type]) -> Type {
    let ra = operand_type_of(a, local_types);
    let rb = operand_type_of(b, local_types);
    let null_lit = |t: &Type| matches!(t, Type::Nullable(inner) if matches!(**inner, Type::Never));
    if null_lit(&ra) {
        return rb;
    }
    if null_lit(&rb) {
        return ra;
    }
    binary_operand_common((&ra, a), (&rb, b))
}

/// The one operand-type rule shared by the typer (`Monomorphizer::
/// binary_operand_type`) and the back ends' comparison-operand pick
/// ([`binary_operand_type`]), given each operand's resolved type and MIR
/// operand. Nullables narrow to their element type (a guarded `int32?`
/// compares as `int32`). Two numbers meet where the checker's operator rule
/// puts them (`brass_typesys::common_operand_type`): an integer-literal
/// constant adapts to the other operand when its value fits (`byte - 32`
/// stays `uint8`), otherwise both take their common type (`byte < 300`
/// compares as `int32`). Any other pair keeps a non-constant operand's type.
pub(super) fn binary_operand_common(
    (ta, a): (&Type, &Operand),
    (tb, b): (&Type, &Operand),
) -> Type {
    let na = unwrap_nullable(ta);
    let nb = unwrap_nullable(tb);
    if let Some(common) = brass_typesys::common_operand_type(
        brass_typesys::NumericOperand::new(na, operand_literal(a)),
        brass_typesys::NumericOperand::new(nb, operand_literal(b)),
    ) {
        return common;
    }
    if matches!(a, Operand::Local(_)) || !matches!(b, Operand::Local(_)) {
        na.clone()
    } else {
        nb.clone()
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

/// The common type of two instances of one nominal declaration that differ
/// only in how much payload information they carry: the union of both
/// substitutions, or `None` when a slot both pin disagrees (or the types are
/// not instances of one declaration). Mirrors the checker's unification of
/// same-id records and sums, which relates exactly these types: an
/// `Opt.Nothing` (no `Some.v` entry) and an `Opt.Some { v: 1 }`
/// (`Some.v=int32`) are one element type, `Opt<Some.v=int32>`.
pub(super) fn join_refinements(a: &Type, b: &Type) -> Option<Type> {
    if a == b {
        return Some(a.clone());
    }
    let join = |x: &NominalType, y: &NominalType| -> Option<NominalType> {
        if x.id != y.id || (x.id < 0 && x.name() != y.name()) {
            return None;
        }
        let mut joined = x.clone();
        for (key, yt) in y.substitution.iter() {
            match x.substitution.get(key) {
                Some(xt) => {
                    let common = join_refinements(xt, yt)?;
                    joined.substitution.insert(key, common);
                }
                None => joined.substitution.insert(key, yt.clone()),
            }
        }
        Some(joined)
    };
    match (a, b) {
        (Type::Record(x), Type::Record(y)) => join(x, y).map(Type::Record),
        (Type::Sum(x), Type::Sum(y)) => join(x, y).map(Type::Sum),
        _ => None,
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
