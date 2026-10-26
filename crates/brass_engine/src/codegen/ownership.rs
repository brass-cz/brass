//! The reference-counting facts the shared walk's retain/release decisions
//! rest on: which types are counted, which rvalues and operands alias an
//! existing object (and so are retained when bound or stored), and when a
//! stored value is a fresh nullable cell whose ownership the slot takes
//! over.

use super::*;

/// Whether a type is a reference-counted heap object the back end tracks with
/// retain/release: strings, records, sums, arrays/slices, tuples, closures, and
/// nullable cells. Aggregates release the heap contents they own recursively
/// through per-type destructors ([`Codegen::release_obj`]: record/variant
/// fields, array elements and the element buffer); a closure releases its
/// captures through the destructor stored in its object
/// ([`Codegen::release_closure`], since the `Fun` type hides the capture
/// types); a string is a leaf, freed directly.
pub fn rc_managed(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Str
            | Type::Record(..)
            | Type::Sum(..)
            | Type::Slice(..)
            | Type::Array(..)
            | Type::Fun(..)
            // A tuple is a fixed heterogeneous heap aggregate (a pointer), tracked
            // and reclaimed like a record.
            | Type::Tuple(..)
            // A nullable is a heap cell (a pointer, null = null), so it is
            // reference-counted: retained when aliased, released when dropped. A cell
            // of a managed value also owns that value (its destructor releases it).
            | Type::Nullable(..)
    )
}

/// Whether storing a `value_ty` value into a `dest_ty` slot is a nullable wrap: a
/// non-nullable value flowing into a nullable cell. `nullable_wrap` builds a fresh
/// cell that already owns its content, so the storing slot takes that ownership
/// without an extra retain (retaining the fresh cell would over-count it -- it is an
/// intermediate, never separately dropped).
pub(super) fn is_nullable_wrap(dest_ty: &Type, value_ty: &Type) -> bool {
    matches!(dest_ty, Type::Nullable(_)) && !matches!(value_ty, Type::Nullable(_))
}

/// Whether an rvalue yields a *second reference to an existing object* (an alias)
/// rather than a freshly-owned value. Aliases must be retained when bound; fresh
/// values (call results, constructions, literals) already own their single
/// reference.
fn is_alias_rvalue(rv: &Rvalue) -> bool {
    matches!(
        rv,
        Rvalue::Use(Operand::Local(_)) | Rvalue::Load(_) | Rvalue::Global(_)
    )
}

/// Whether an operand is an alias of an existing object (a local read), as opposed to
/// a fresh value (a literal constant). Storing an alias into an aggregate must retain
/// it (a second reference); a fresh constant is already owned at count 1 and the
/// aggregate takes that ownership -- retaining it would leak, since a constant has no
/// local binding whose drop would balance the retain.
pub(super) fn operand_is_alias(op: &Operand) -> bool {
    matches!(op, Operand::Local(_))
}

/// Whether an rvalue *bound to a local* yields an alias of an existing managed
/// object and so must be retained: a plain alias rvalue, or `to_string`/`string.from`
/// of a string (its identity result is a second reference to the argument). The
/// conversion is recognized here rather than in the back end's leaf so that an
/// unbound, transient conversion (e.g. inside `print`) is not retained and leaked.
pub(super) fn binds_alias(rv: &Rvalue, local_types: &[Type]) -> bool {
    if is_alias_rvalue(rv) {
        return true;
    }
    // Rendering a string is the identity, so the result aliases the argument. Both
    // the implicit interpolation builtin (`to_string`) and the explicit `string.from`
    // static call lower to that same identity leaf, so a bound result of either must
    // be retained -- otherwise its later drop over-releases the borrowed argument
    // (e.g. `let a = string.from(key)` used twice double-frees `key`). For a
    // non-string argument the conversion allocates a fresh owned string, not an alias.
    let str_identity_arg = match rv {
        Rvalue::Call(Callee::Builtin(name), args) if name == "to_string" => args.first(),
        Rvalue::Call(Callee::Static { ty, method }, args) if ty == "string" && method == "from" => {
            args.first()
        }
        _ => None,
    };
    if let Some(arg) = str_identity_arg {
        return matches!(operand_type_of(arg, local_types), Type::Str);
    }
    if let Rvalue::Call(Callee::Builtin(name), args) = rv
        && name == "__nonnull"
        && let Some(arg) = args.first()
    {
        return rc_managed(unwrap_nullable(&operand_type_of(arg, local_types)));
    }
    false
}

/// Whether a discarded call result borrows a managed value already owned by a
/// local. Identity conversions and nullable narrowing return their argument;
/// releasing that borrowed result would consume the local's reference. A
/// constant argument has no other owner, so its identity result remains an
/// owned temporary and is released normally.
pub(super) fn discarded_call_borrows_alias(rv: &Rvalue, local_types: &[Type]) -> bool {
    binds_alias(rv, local_types)
        && matches!(
            rv,
            Rvalue::Call(_, args) if matches!(args.first(), Some(Operand::Local(_)))
        )
}
