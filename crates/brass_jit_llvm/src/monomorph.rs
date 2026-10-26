//! LLVM symbol names for monomorphized instances, and the table of declared
//! LLVM functions.
//!
//! `brass_engine` names every instance with a collision-free engine symbol
//! that already encodes its concrete argument types; [`mangle_fn`] maps that
//! symbol injectively onto an LLVM function name, so the code generator, the
//! lazy JIT's lookups and its deferred call sites all agree on one name per
//! instance.

use fxhash::FxHashMap as HashMap;

use inkwell::values::FunctionValue;

/// Injective LLVM-name encoding of an engine symbol: ASCII alphanumerics pass
/// through; every other character (including `_` itself) becomes `_{hex}_`, its
/// code point framed by underscores. Every `_` in the output therefore belongs
/// to an escape, so decoding is unambiguous and two distinct engine symbols
/// (e.g. `probe__int32?[]` and `probe__int32[]?`, which folding every
/// punctuation character to `_` would merge) never map to the same LLVM
/// function name.
fn sanitize(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        if c.is_ascii_alphanumeric() {
            out.push(c);
        } else {
            out.push('_');
            out.push_str(&format!("{:x}", c as u32));
            out.push('_');
        }
    }
    out
}

/// The LLVM function name of the instance whose engine symbol is `name`
/// (see `brass_engine::instance_symbol`).
pub fn mangle_fn(name: &str) -> String {
    // Compiler-synthesized instances (module inits, methods, statics, closures)
    // are tagged by `brass_engine` with a reserved sigil that no source
    // identifier can contain. Route them to a prefix disjoint from `pp_fn_`, so
    // a user `fun init0` and the first module init never produce the same LLVM
    // symbol whatever the sigil's encoding.
    if let Some(rest) = name.strip_prefix(brass_engine::SYNTH_SIGIL) {
        return format!("pp_synth_{}", sanitize(rest));
    }
    format!("pp_fn_{}", sanitize(name))
}

/// The LLVM functions declared in the module being built, keyed by their
/// mangled name.
#[derive(Default)]
pub struct FnCache<'ctx> {
    pub map: HashMap<String, FunctionValue<'ctx>>,
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Two engine symbols that differ only in punctuation stay distinct: every
    /// non-alphanumeric character is escaped by its code point.
    #[test]
    fn mangling_is_injective_over_punctuation() {
        assert_ne!(mangle_fn("probe__int32?[]"), mangle_fn("probe__int32[]?"));
        assert_ne!(mangle_fn("a_b"), mangle_fn("a__b"));
    }

    /// A compiler-synthesized instance never shares an LLVM name with a user
    /// function spelled like it.
    #[test]
    fn synthesized_instances_use_a_disjoint_prefix() {
        let synthesized = format!("{}init0", brass_engine::SYNTH_SIGIL);
        assert_ne!(mangle_fn(&synthesized), mangle_fn("init0"));
        assert!(mangle_fn(&synthesized).starts_with("pp_synth_"));
    }
}
