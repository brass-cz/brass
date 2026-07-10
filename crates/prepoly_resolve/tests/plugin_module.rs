//! Synthesizing a Prepoly module from a real plugin library's manifest.

#![cfg(not(target_family = "wasm"))]

use prepoly_plugin_host::fixture;
use prepoly_resolve::plugin::synthesize_plugin_module;

/// The generated module is valid Prepoly source carrying, per plugin
/// function: the Rust doc comment, a fully annotated signature, and a body
/// forwarding to the `_plugin_call_*` builtin with path/name/signature.
#[test]
fn fixture_manifest_synthesizes_wrappers() {
    let lib = fixture::build_testlib();
    let src = synthesize_plugin_module(&lib).expect("synthesize");

    // Doc comment and annotated signature, straight from the Rust source.
    assert!(src.contains("/**\nAdds two integers.\n*/"), "{src}");
    assert!(
        src.contains("fun add(a: int64, b: int64) -> int64 {"),
        "{src}"
    );
    // The body forwards to the int-returning builtin with the encoded sig.
    assert!(src.contains("return _plugin_call_i(\""), "{src}");
    assert!(src.contains("\"add\", \"ii:i\", a, b)"), "{src}");

    // A fallible function wraps through the fallible builtin and declares `!`.
    assert!(
        src.contains("fun checked_div(a: int64, b: int64) -> int64! {"),
        "{src}"
    );
    assert!(src.contains("_plugin_fcall_i(\""), "{src}");

    // Every supported type maps to its Prepoly spelling, arrays included:
    // `uint8[]` is its own type, `T[]` nests, and an array returns too.
    assert!(
        src.contains("fun byte_len(data: uint8[]) -> int64 {"),
        "{src}"
    );
    assert!(
        src.contains("fun join(parts: string[], sep: string) -> string {"),
        "{src}"
    );
    assert!(
        src.contains("fun split(text: string, sep: string) -> string[] {"),
        "{src}"
    );
    assert!(
        src.contains("fun row_lengths(rows: string[][]) -> int64[] {"),
        "{src}"
    );
    // The array return picks the `a`-prefixed builtin name.
    assert!(src.contains("return _plugin_call_as(\""), "{src}");
    assert!(src.contains("\"row_lengths\", \"aas:ai\""), "{src}");
    assert!(
        src.contains("fun scale(x: float64, factor: float64) -> float64 {"),
        "{src}"
    );
    assert!(src.contains("fun is_even(v: int64) -> bool {"), "{src}");
    // A void function has no annotation and calls as a statement.
    assert!(
        src.contains("fun undocumented() {\n    _plugin_call_v(\""),
        "{src}"
    );

    // The whole module parses.
    prepoly_parser::parse(&src).expect("synthesized module parses");
}
