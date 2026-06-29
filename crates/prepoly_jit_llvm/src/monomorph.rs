//! Symbol mangling and the compiled-function cache (DESIGN.md 7.1).
//!
//! Implementation mode (temporary): every callable is compiled once against the
//! uniform tagged-value ABI (`layout::Abi::fn_type`), so a single body serves
//! every concrete type and this "monomorphization cache" is a name -> LLVM-
//! function map; the deferred path (DESIGN.md 7.3) is realized by runtime tag
//! dispatch rather than per-type recompilation. DESIGN.md 7-8 describe typed
//! monomorphization as the target backend; the uniform ABI is a compatibility
//! layer to be retired or restricted to dynamic/builtin boundaries, not the
//! final language design (DESIGN.md 8.1; PLAN.md R5). The mangling is shared
//! with the driver so it can resolve each symbol's JIT address for the runtime
//! dispatch tables.

use std::collections::HashMap;

use inkwell::values::FunctionValue;
use prepoly_hir::{FloatKind, IntKind, Type};

fn sanitize(s: &str) -> String {
    s.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

pub fn mangle_fn(name: &str) -> String {
    // Compiler-synthesized instances (module inits, methods, statics, closures)
    // are tagged by `prepoly_engine` with a reserved sigil that no source
    // identifier can contain. Route them to a prefix disjoint from `pp_fn_` so a
    // user `fun init0` and the first module init never produce the same LLVM
    // symbol. `sanitize` would otherwise fold the sigil to `_`, re-colliding them.
    if let Some(rest) = name.strip_prefix(prepoly_engine::SYNTH_SIGIL) {
        return format!("pp_synth_{}", sanitize(rest));
    }
    format!("pp_fn_{}", sanitize(name))
}

/// `qualifier` is a type name (record/static) or `Type.Variant` (sum method).
pub fn mangle_method(qualifier: &str, method: &str) -> String {
    format!("pp_m_{}_{}", sanitize(qualifier), sanitize(method))
}

pub fn mangle_init(idx: usize) -> String {
    format!("pp_init_{idx}")
}

/// A short, collision-resistant mangling of a type, for naming a monomorphized
/// instance (PLAN.md R5 stage 2). Distinct concrete types yield distinct
/// strings, so a function specialized for `int32` and for `string` gets two
/// symbols. Heap/nominal types include their nominal id to stay unique across
/// modules that share a display name (R2).
pub fn type_mangle(ty: &Type) -> String {
    match ty {
        Type::Bool => "b".into(),
        Type::Int(k) => int_code(*k).into(),
        Type::Float(FloatKind::F32) => "f32".into(),
        Type::Float(FloatKind::F64) => "f64".into(),
        Type::Str => "str".into(),
        Type::Void => "void".into(),
        Type::Never => "never".into(),
        Type::Record(n) => format!("r{}", n.id),
        Type::Sum(n) => format!("s{}", n.id),
        Type::Array(inner, len) => format!("a{len}_{}", type_mangle(inner)),
        Type::Slice(inner) => format!("sl_{}", type_mangle(inner)),
        Type::Tuple(elems) => {
            let es: Vec<String> = elems.iter().map(type_mangle).collect();
            format!("tup{}_{}", elems.len(), es.join("_"))
        }
        Type::Fun(params, ret) => {
            let ps: Vec<String> = params.iter().map(type_mangle).collect();
            format!("fn{}_{}", ps.join("_"), type_mangle(ret))
        }
        Type::Nullable(inner) => format!("opt_{}", type_mangle(inner)),
        Type::ConstOf(inner) | Type::Mut(inner) | Type::Ref(inner) => type_mangle(inner),
        Type::Unknown(id) => format!("u{id}"),
        Type::SelfType => "self".into(),
    }
}

fn int_code(k: IntKind) -> &'static str {
    match k {
        IntKind::I8 => "i8",
        IntKind::I16 => "i16",
        IntKind::I32 => "i32",
        IntKind::I64 => "i64",
        IntKind::U8 => "u8",
        IntKind::U16 => "u16",
        IntKind::U32 => "u32",
        IntKind::U64 => "u64",
    }
}

/// The symbol of one monomorphized function instance: the base function symbol
/// plus the concrete argument types it is specialized for (PLAN.md R5 stage 2,
/// 5). With the typed backend this names a distinct LLVM function per instance;
/// the uniform ABI compiles a single `mangle_fn` body for all instances.
pub fn mangle_fn_instance(symbol: &str, arg_types: &[Type]) -> String {
    if arg_types.is_empty() {
        return mangle_fn(symbol);
    }
    let args: Vec<String> = arg_types.iter().map(type_mangle).collect();
    format!("{}__{}", mangle_fn(symbol), sanitize(&args.join("_")))
}

/// As [`mangle_fn_instance`] but for a method instance, keyed by the receiver
/// type/variant qualifier and the concrete argument types.
pub fn mangle_method_instance(qualifier: &str, method: &str, arg_types: &[Type]) -> String {
    if arg_types.is_empty() {
        return mangle_method(qualifier, method);
    }
    let args: Vec<String> = arg_types.iter().map(type_mangle).collect();
    format!(
        "{}__{}",
        mangle_method(qualifier, method),
        sanitize(&args.join("_"))
    )
}

pub fn mangle_closure(idx: usize) -> String {
    format!("pp_clo_{idx}")
}

#[derive(Default)]
pub struct FnCache<'ctx> {
    pub map: HashMap<String, FunctionValue<'ctx>>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use prepoly_hir::NominalType;

    #[test]
    fn instances_differ_by_argument_type() {
        // PLAN.md R5: a function specialized for int32 and for string is two
        // distinct instances with distinct symbols.
        let for_int = mangle_fn_instance("id", &[Type::Int(IntKind::I32)]);
        let for_str = mangle_fn_instance("id", &[Type::Str]);
        assert_ne!(for_int, for_str);
        assert!(for_int.starts_with(&mangle_fn("id")));
        assert!(for_str.starts_with(&mangle_fn("id")));
    }

    #[test]
    fn zero_arg_instance_is_the_base_symbol() {
        assert_eq!(mangle_fn_instance("main", &[]), mangle_fn("main"));
    }

    #[test]
    fn same_named_nominal_types_mangle_distinctly_by_id() {
        // Two `Shape` types in different modules have different ids (R2), so
        // their instances do not collide.
        let a = type_mangle(&Type::Record(NominalType::new(5, "Shape")));
        let b = type_mangle(&Type::Record(NominalType::new(6, "Shape")));
        assert_ne!(a, b);
    }

    #[test]
    fn method_instances_differ_by_argument_type() {
        let i = mangle_method_instance("Vec2", "scale", &[Type::Float(FloatKind::F64)]);
        let s = mangle_method_instance("Vec2", "scale", &[Type::Str]);
        assert_ne!(i, s);
    }
}
