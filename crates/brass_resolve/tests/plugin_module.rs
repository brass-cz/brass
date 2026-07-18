//! Synthesizing a Brass module from a real plugin library's manifest.

#![cfg(not(target_family = "wasm"))]

use std::fs;
use std::path::PathBuf;

use brass_plugin_host::{PluginFunction, PluginManifest, ValueType, fixture};
use brass_resolve::plugin::{synthesize_plugin_module, synthesize_source};
use brass_resolve::{inject_module_path, reinject_plugin_path};

/// A manifest holding one exported function of `name` taking no arguments and
/// returning nothing, optionally documented.
fn manifest_of(names: &[&str], doc: Option<&str>) -> PluginManifest {
    PluginManifest {
        functions: names
            .iter()
            .enumerate()
            .map(|(i, name)| PluginFunction {
                name: (*name).to_string(),
                doc: doc.map(str::to_string),
                params: Vec::new(),
                ret: ValueType::Void,
                fallible: false,
                index: i as u32,
            })
            .collect(),
    }
}

/// The generated module is valid Brass source carrying, per plugin
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

    // Every supported type maps to its Brass spelling, arrays included:
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

    // A Brass keyword and a runtime builtin are legal Rust function names.
    // Their wrappers are renamed, but each still dispatches to the plugin's
    // own name, which the call carries as a string.
    assert!(src.contains("fun match_(a0: int64) -> int64 {"), "{src}");
    assert!(src.contains("\"match\", \"i:i\", a0)"), "{src}");
    assert!(src.contains("fun len_(a0: string) -> int64 {"), "{src}");
    assert!(src.contains("\"len\", \"s:i\", a0)"), "{src}");

    // A `/*` in a doc comment would open a nested block comment the wrapper's
    // `*/` then only half-closes; both delimiters are neutralized.
    assert!(src.contains("nested / * block comment * /"), "{src}");

    // The whole module parses.
    brass_parser::parse(&src).expect("synthesized module parses");
}

/// A cached synthesized module keeps its spans but receives the library path
/// found by the current machine's normal import resolution.
#[test]
fn synthesized_wrapper_paths_can_be_reanchored() {
    let src = synthesize_source(&manifest_of(&["run"], None), "/build/libprocess.so")
        .expect("synthesize");
    let mut ast = brass_parser::parse(&src).expect("parse synthesized module");
    inject_module_path(
        &mut ast,
        "<plugin:/build/libprocess.so>",
        brass_parser::Span::new(0, 0),
    );

    reinject_plugin_path(&mut ast, "/installed/libprocess.so");

    let ast = format!("{ast:?}");
    assert!(!ast.contains("/build/libprocess.so"), "{ast}");
    assert!(ast.contains("/installed/libprocess.so"), "{ast}");
    assert!(ast.contains("<plugin:/installed/libprocess.so>"), "{ast}");
}

/// The library path is embedded in a Brass string literal, where `{` opens
/// interpolation. A checkout under a `{`-containing directory must still
/// synthesize a module that parses and names the right library.
#[test]
fn a_brace_in_the_library_path_is_escaped() {
    let lib = fixture::build_testlib();
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("plug{in}s");
    fs::create_dir_all(&dir).expect("create the brace-named directory");
    let placed = dir.join(lib.file_name().expect("library file name"));
    fs::copy(&lib, &placed).expect("copy the library");

    let src = synthesize_plugin_module(&placed).expect("synthesize");
    assert!(src.contains("plug\\{in}s"), "{src}");
    brass_parser::parse(&src).expect("synthesized module parses");
}

/// Renaming can make two exported functions collide (`match` and `match_`).
/// That is a per-plugin error naming both, not a duplicate-definition error
/// inside a module the user never sees.
#[test]
fn a_rename_collision_is_reported() {
    let err = synthesize_source(&manifest_of(&["match", "match_"], None), "lib.so")
        .expect_err("collision");
    assert!(
        err.contains("collides with another exported function"),
        "{err}"
    );

    // Distinct names that need no renaming still synthesize.
    synthesize_source(&manifest_of(&["a", "b"], None), "lib.so").expect("no collision");
}

/// A doc comment consisting of a lone `/*` has no closer to rewrite, yet still
/// raises the nesting depth of the wrapper's own block comment.
#[test]
fn an_unbalanced_block_comment_opener_in_a_doc_is_neutralized() {
    let src = synthesize_source(
        &manifest_of(&["f"], Some("Strips /* comments */ and a lone /*")),
        "l",
    )
    .expect("synthesize");
    assert!(!src.contains("/*\n"), "no bare opener survives:\n{src}");
    brass_parser::parse(&src).expect("synthesized module parses");
}
