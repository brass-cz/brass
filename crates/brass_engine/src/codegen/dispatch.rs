//! How a call site dispatches: one classification of a callee at concrete
//! argument types, which both emission and result typing branch on.

use super::*;

/// How a call site dispatches, derived from the callee and the concrete
/// argument types. [`Codegen::codegen_call`] (emission) and
/// [`Codegen::call_result_type`] (result typing) both branch on this one
/// classification, so the two can never disagree about which primitive or
/// instance a call resolves to.
pub(super) enum CallKind<'c> {
    /// `arr.push(v)`: a growable-array append, not a user method.
    ArrayPush,
    /// `arr.insert(i, v)`: a growable-array insertion (`_array_insert`).
    ArrayInsert,
    /// `arr.remove(i)`: a growable-array removal (`_array_remove`) returning
    /// the removed element.
    ArrayRemove,
    /// `arr.pop()`: removal of the last element (`_array_pop`), returned as a
    /// nullable.
    ArrayPop,
    /// `arr.len()` / `s.len()`: the length builtin in method form.
    Len,
    /// A runtime-recognized numeric/string conversion `ty.method(arg)` (not a
    /// user static).
    NumericConv { ty: &'c str, method: &'c str },
    /// Typed I/O: `print`/`println` write to stdout directly.
    Io(&'c str),
    /// A MIR-internal builtin (`match` lowering, runtime primitives).
    Builtin(&'c str),
    /// An indirect (closure) call through a runtime function value.
    Indirect(&'c Operand),
    /// A monomorphized instance, called by its resolved symbol.
    Instance(String),
    /// A `"{v}"` segment of a nullable whose inner type renders through the
    /// USER `display` instance named here ([`nullable_display_instance`]):
    /// `null` when absent, the instance's result on the unwrapped value when
    /// present.
    NullableDisplay(String),
}

/// Classify how `callee` dispatches for these concrete argument types. The
/// receiver checks strip a top-level nullable (a narrowed `T[]?` receiver still
/// carries its declared nullable type in MIR).
pub(super) fn classify_call<'c>(
    program: &MonoProgram,
    f: &MonoFunction,
    callee: &'c Callee,
    arg_types: &[Type],
    dest_ty: &Type,
) -> CallKind<'c> {
    match callee {
        Callee::Numeric { inner, site } => match f.keyed.get(site) {
            Some(target) => CallKind::Instance(target.clone()),
            None => classify_call(program, f, inner, arg_types, dest_ty),
        },
        Callee::Method(name) => classify_method(program, name, arg_types),
        // A reflective call dispatches like a method call naming the
        // specialization this instance resolved it to.
        Callee::Keyed { site, method } => {
            let target = f.keyed.get(site).unwrap_or(method);
            classify_method(program, target, arg_types)
        }
        Callee::Static { ty, method } if numeric_conv_ret(ty, method).is_some() => {
            CallKind::NumericConv { ty, method }
        }
        // The destination type keys a return-polymorphic, no-argument
        // constructor (a witness-free `new()`) to the same instance the
        // monomorphizer created for this result type.
        Callee::Static { ty, method } => {
            CallKind::Instance(static_symbol(ty, method, arg_types, Some(dest_ty)))
        }
        Callee::Free(base) if base == "print" || base == "println" => CallKind::Io(base),
        Callee::Free(base) => CallKind::Instance(instance_symbol(base, arg_types)),
        Callee::NumericFree { base, site } => CallKind::Instance(
            f.keyed
                .get(site)
                .cloned()
                .unwrap_or_else(|| instance_symbol(base, arg_types)),
        ),
        // A `to_string` segment (`"{v}"`) routes to the USER `display`
        // instance the monomorphizer created when the value's type declares
        // one; everything else keeps the built-in renderer.
        Callee::Builtin(name) if name == "to_string" => {
            let Some(ty) = arg_types.first() else {
                return CallKind::Builtin(name);
            };
            if let Some(inst) = display_instance(program, ty) {
                CallKind::Instance(inst.symbol.clone())
            } else if let Some(inst) = nullable_display_instance(program, ty) {
                CallKind::NullableDisplay(inst.symbol.clone())
            } else {
                CallKind::Builtin(name)
            }
        }
        Callee::Builtin(name) => CallKind::Builtin(name),
        Callee::Indirect(op) => CallKind::Indirect(op),
    }
}

/// [`classify_call`] of the method call `recv.name(..)` (`arg_types[0]` is
/// the receiver).
fn classify_method<'c>(program: &MonoProgram, name: &str, arg_types: &[Type]) -> CallKind<'c> {
    let slice_receiver = || matches!(arg_types.first().map(unwrap_nullable), Some(Type::Slice(_)));
    match name {
        "push" if slice_receiver() => CallKind::ArrayPush,
        "insert" if slice_receiver() => CallKind::ArrayInsert,
        "remove" if slice_receiver() => CallKind::ArrayRemove,
        "pop" if slice_receiver() => CallKind::ArrayPop,
        "len"
            if matches!(
                arg_types.first().map(unwrap_nullable),
                Some(Type::Slice(_) | Type::Array(..) | Type::Str)
            ) =>
        {
            CallKind::Len
        }
        // Instance method. A nominal method instance is keyed by
        // `method_symbol`; a stdlib primitive/array method (`fun
        // string.split`) by its class-qualified symbol. The type checker has
        // already rejected any other `recv.m()`.
        _ => {
            let msym = method_symbol(name, arg_types);
            let target = if program.lookup(&msym).is_some() {
                msym
            } else if let Some(psym) = prim_method_instance(program, name, arg_types) {
                psym
            } else if name == "debug" {
                // The built-in `debug`: a receiver with neither a user nor a
                // core primitive `debug` renders through the runtime's
                // traditional formatter, exactly like a `"{v}"` segment.
                return CallKind::Builtin("to_string");
            } else {
                instance_symbol(name, arg_types)
            };
            CallKind::Instance(target)
        }
    }
}
