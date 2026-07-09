//! Instance symbol naming: every monomorphized function, method,
//! constructor, and closure instance gets a collision-free symbol
//! derived from its base name and concrete type arguments.

use super::*;

pub(super) use prepoly_hir::type_key;

/// Marks a compiler-synthesized instance symbol (a module init, method, static,
/// or closure) so it occupies a namespace disjoint from user function symbols.
/// `$` cannot appear in a source identifier, so a user `fun init0` (symbol
/// `init0`) never collides with the first module init (`$init0`) in the instance
/// map, and the back end maps the two to distinct LLVM names. Must match the
/// prefix `prepoly_jit_llvm`'s `mangle_fn` recognizes.
pub const SYNTH_SIGIL: char = '$';

/// The canonical instance symbol for `base` specialized to `type_args`. Distinct
/// type tuples yield distinct strings, so instances never collide: the argument
/// section is a `$$`-prefixed join of collision-resistant [`type_key`]s (no base
/// symbol contains `$$`, and no key contains `$`, so the base/argument split is
/// unambiguous -- a display-based join would let `(A_B, C)` and `(A, B_C)` share
/// a symbol and silently reuse a body typed for different argument types).
pub fn instance_symbol(base: &str, type_args: &[Type]) -> String {
    if type_args.is_empty() {
        base.to_string()
    } else {
        let args = type_args.iter().map(type_key).collect::<Vec<_>>().join("_");
        format!("{base}$${args}")
    }
}

/// Instance symbol of an instance-method call. `type_args[0]` is the receiver
/// type, so the symbol is unique per receiver layout; the method name keeps
/// distinct methods apart. Derivable from types alone (no HIR program), so the
/// monomorphizer and the back end agree.
///
/// A nullable receiver is keyed by its inner type: the checker only accepts a
/// method call on a `T?` it has proven non-null, and the call boundary
/// unwraps the cell (`codegen_operand` coerces to the instance's `self`
/// type), so the narrowed and the plain receiver share one instance.
pub fn method_symbol(method: &str, type_args: &[Type]) -> String {
    let base = format!("{SYNTH_SIGIL}m_{method}");
    if let Some(Type::Nullable(inner)) = type_args.first() {
        let mut args = type_args.to_vec();
        args[0] = (**inner).clone();
        return instance_symbol(&base, &args);
    }
    instance_symbol(&base, type_args)
}

/// Instance symbol of a static call `Type.method(args)`.
///
/// A *no-argument* static that returns an aggregate (record/sum/array) is
/// return-polymorphic: a witness-free `HashMap.new()` whose element types are
/// fixed only by the caller. Its arguments alone do not distinguish
/// `HashMap<string,int32>` from `HashMap<int32,int32>`, so the result type is
/// folded into the key for those, giving each a distinct instance. Statics with
/// arguments are keyed by their arguments alone (the result is a function of
/// them), so non-generic statics are unaffected. The monomorphizer passes the
/// resolved result here; both back ends pass the call's destination type, which
/// is the same value, so all three derive the identical symbol.
pub fn static_symbol(ty: &str, method: &str, type_args: &[Type], result: Option<&Type>) -> String {
    let mut key = type_args.to_vec();
    if type_args.is_empty()
        && let Some(r) = result
        && is_return_polymorphic_result(r)
    {
        key.push(r.clone());
    }
    // The sigil also separates the type from the method: a type symbol may
    // itself contain `_` (`A_B.get` vs `A.B_get` must not share a symbol), and
    // no identifier can contain the sigil.
    instance_symbol(&format!("{SYNTH_SIGIL}s_{ty}{SYNTH_SIGIL}{method}"), &key)
}

/// Whether a no-argument static's result type can vary by caller and so must be
/// folded into its instance key: a record/sum built around inferred field types
/// (a witness-free constructor). Scalars/strings/void/arrays are left out,
/// keeping their symbols unchanged. Matches the seeding filter so the
/// monomorphizer and both back ends key these constructors identically.
pub(super) fn is_return_polymorphic_result(ty: &Type) -> bool {
    matches!(ty, Type::Record(_) | Type::Sum(_))
}

/// The monomorphized instance symbol for a `recv.name(args)` call that resolves
/// to a stdlib primitive/array method, when such an instance exists in
/// `program`. The receiver's class ([`Type::primitive_class`]) plus the method
/// name reconstruct the body's class-qualified symbol (the same scheme HIR
/// lowering used), which `instance_symbol` keys by argument types. Lets the back
/// ends route the call without carrying the HIR `primitive_methods` table.
pub fn prim_method_instance(
    program: &MonoProgram,
    name: &str,
    arg_types: &[Type],
) -> Option<String> {
    // A narrowed nullable receiver dispatches as its inner class, exactly as
    // in `method_symbol`.
    let mut args = arg_types.to_vec();
    if let Some(Type::Nullable(inner)) = args.first() {
        args[0] = (**inner).clone();
    }
    let class = args.first()?.primitive_class()?;
    let sym = instance_symbol(&prepoly_hir::prim_method_symbol(class, name), &args);
    program.lookup(&sym).map(|_| sym)
}

/// Instance symbol of a closure: distinct per closure id, captured types, and
/// parameter types. Derivable from types alone so the monomorphizer and back end
/// agree.
pub fn closure_symbol(id: ClosureId, capture_types: &[Type], param_types: &[Type]) -> String {
    let mut args = capture_types.to_vec();
    args.extend_from_slice(param_types);
    instance_symbol(&format!("{SYNTH_SIGIL}clo{}", id.index()), &args)
}
