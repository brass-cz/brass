//! Declaration-independent builtin results shared by light analysis and
//! producer inventory. Callers handle visibility and shadowing before use.

use crate::{FloatKind, IntKind, Type};

/// Return family without solving arguments. `input_declared` preserves the
/// prelude's inferred error payload instead of using the fallback signature.
#[inline]
pub fn builtin_return(name: &str, input_declared: impl FnOnce() -> bool) -> Option<Type> {
    if let Some(ret) = crate::plugin_builtin_return(name) {
        return Some(ret);
    }
    match name {
        "_print_str" | "_println_str" => Some(Type::Void),
        "_stdin_read" => Some(Type::result(
            Type::Slice(Box::new(Type::Int(IntKind::U8))),
            Type::Str,
        )),
        "_argv" => Some(Type::Slice(Box::new(Type::Str))),
        "_flush" | "_panic" => Some(Type::Void),
        // The prelude declares the real `input` (an inferred-fallible
        // `string!` whose Err is the prelude `Error`); its return comes
        // from the precompute table like any function's. This type only
        // stands in for a program without the prelude, as in the full
        // check (`builtin_function_type`).
        "input" if !input_declared() => Some(Type::result(Type::Str, Type::Str)),
        "len" => Some(Type::Int(IntKind::I64)),
        "print" | "println" | "assert" => Some(Type::Void),
        "_string_concat" | "_string_slice" => Some(Type::Str),
        // The character at a byte offset, or null past the end or inside a
        // multibyte character.
        "_string_char_at" => Some(Type::Nullable(Box::new(Type::Str))),
        "_string_bytes" => Some(Type::Slice(Box::new(Type::Int(IntKind::U8)))),
        "_string_from_bytes" => Some(Type::result(Type::Str, Type::Str)),
        "_string_find" => Some(Type::Nullable(Box::new(Type::Int(IntKind::I64)))),
        "_string_cmp" => Some(Type::Int(IntKind::I32)),
        "_int_to_string" | "_float_to_string" => Some(Type::Str),
        "_int_parse" => Some(Type::result(Type::Int(IntKind::I64), Type::Str)),
        "_float_parse" => Some(Type::result(Type::Float(FloatKind::F64), Type::Str)),
        "_int_to_float" | "_float_sqrt" | "_float_floor" | "_float_ceil" | "_float_pow" => {
            Some(Type::Float(FloatKind::F64))
        }
        "_float_to_int" | "_int_narrow" => Some(Type::result(Type::Int(IntKind::I64), Type::Str)),
        "_int_widen" => Some(Type::Int(IntKind::I64)),
        "spawn" | "sync" | "_cown" | "_freeze" => Some(Type::Void),
        _ => None,
    }
}
