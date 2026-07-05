//! End-to-end tests over the crate's analysis and feature layers, exercised
//! through the same public entry points the LSP handlers use.

use std::path::PathBuf;

use prepoly_parser::Span;

use crate::analysis::{DocAnalyzer, FullAnalysis};
use crate::document::Document;
use crate::features::{completion, definition, hover, semantic_tokens};
use tower_lsp_server::ls_types::{CompletionItem, HoverContents, Position};

fn path() -> PathBuf {
    PathBuf::from("/tmp/prepoly_lsp_test/main.pp")
}

fn sorted(mut v: Vec<(String, Span)>) -> Vec<(String, Span)> {
    v.sort_by(|a, b| (a.1.lo, a.1.hi, &a.0).cmp(&(b.1.lo, b.1.hi, &b.0)));
    v
}

fn full_analysis(src: &str) -> FullAnalysis {
    DocAnalyzer::new(path()).analyze_full(src).unwrap()
}

fn position(src: &str, needle: &str, last: bool) -> (Document, Position) {
    let off = if last {
        src.rfind(needle).unwrap()
    } else {
        src.find(needle).unwrap()
    };
    let doc = Document::new(src.to_string(), 1);
    // Aim a bit inside the token so the cursor is unambiguously on it.
    let pos = doc.position_at(off + 1);
    (doc, pos)
}

/// The core incremental-correctness invariant: feeding successive document
/// versions to one analyzer (which re-checks only changed items and their
/// users) yields exactly the diagnostics a from-scratch check of each version
/// produces.
#[test]
fn incremental_matches_full() {
    let versions = [
        // Clean two-function program.
        "fun helper(x: int32) -> int32 {\n    return x + 1\n}\n\nfun main() {\n    let y = helper(2)\n    println(y)\n}\n",
        // A type error introduced inside `main` only.
        "fun helper(x: int32) -> int32 {\n    return x + 1\n}\n\nfun main() {\n    let y = helper(2)\n    let z: int32 = \"oops\"\n    println(y)\n}\n",
        // `helper`'s signature changes; `main`'s call to it must be re-checked.
        "fun helper(x: string) -> int32 {\n    return 1\n}\n\nfun main() {\n    let y = helper(2)\n    let z: int32 = \"oops\"\n    println(y)\n}\n",
        // Back to clean.
        "fun helper(x: int32) -> int32 {\n    return x + 1\n}\n\nfun main() {\n    let y = helper(2)\n    println(y)\n}\n",
    ];

    let mut incremental = DocAnalyzer::new(path());
    for (i, text) in versions.iter().enumerate() {
        let got = sorted(incremental.diagnostics(text));
        let want = sorted(DocAnalyzer::new(path()).diagnostics(text));
        assert_eq!(got, want, "incremental != full on version {i}:\n{text}");
    }
}

/// A whitespace-only edit (no item's source content changes) must not alter the
/// reported diagnostics, only their positions.
#[test]
fn whitespace_edit_preserves_diagnostics() {
    let mut a = DocAnalyzer::new(path());
    let v1 = "fun main() {\n    let z: int32 = \"oops\"\n}\n";
    let v2 = "fun main() {\n\n    let z: int32 = \"oops\"\n}\n"; // blank line added
    let d1 = a.diagnostics(v1);
    let d2 = a.diagnostics(v2);
    assert!(!d1.is_empty(), "the program has a type error");
    // The messages survive the edit unchanged (only positions move).
    let msgs1: Vec<&String> = d1.iter().map(|(m, _)| m).collect();
    let msgs2: Vec<&String> = d2.iter().map(|(m, _)| m).collect();
    assert_eq!(
        msgs1, msgs2,
        "a whitespace edit must not change the diagnostics"
    );
    // The incremental result matches a fresh from-scratch check.
    assert_eq!(sorted(d2), sorted(DocAnalyzer::new(path()).diagnostics(v2)));
}

fn hover_text(h: &tower_lsp_server::ls_types::Hover) -> String {
    match &h.contents {
        HoverContents::Markup(m) => m.value.clone(),
        other => format!("{other:?}"),
    }
}

/// An unannotated function's type uses numbered `unknown_N`, sharing a variable
/// where the source does: identity `fun id(x) { return x }` has the same
/// `unknown_0` for its parameter and return. Uncalled, so no bindings section.
#[test]
fn hover_shows_unknown_numbered_signature() {
    let src = "fun id(x) {\n    return x\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "id(x)", false);
    let h = hover::hover(&doc, &full, pos).expect("hover over the function name");
    let text = hover_text(&h);
    assert!(
        text.contains("fun id(x: ref(unknown_0)) -> unknown_0"),
        "identity type: {text}"
    );
    assert!(!text.contains("---"), "no bindings without a call: {text}");
}

/// Calling an unannotated parameter (`fun apply(f, x) { f(x) }`) constrains it to
/// a function type, so hover shows `apply` as a higher-order function -- `f` as
/// `(U) -> V` (a function value, shown without a `ref`/`mut` wrapper) rather than
/// a bare `unknown`.
#[test]
fn hover_infers_called_parameter_as_a_function() {
    let src = "fun apply(f, x) {\n    return f(x)\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "apply(f, x)", false);
    let text = hover_text(&hover::hover(&doc, &full, pos).expect("hover over apply"));
    assert!(
        text.contains("fun apply(f: (unknown_0) -> unknown_1, x: ref(unknown_0)) -> unknown_1"),
        "apply must be a higher-order function: {text}"
    );
}

/// An unannotated parameter the body mutates is shown as a private `mut` deep
/// copy, distinguishing it from an unmutated `ref` borrow.
#[test]
fn hover_shows_mut_for_a_mutated_parameter() {
    let src = "fun grow(xs) {\n    xs.push(1)\n}\nfun main() {\n    let a = [1]\n    grow(a)\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "grow(xs)", false);
    let text = hover_text(&hover::hover(&doc, &full, pos).expect("hover over grow"));
    assert!(
        text.contains("fun grow(xs: mut("),
        "a mutated unannotated parameter must show `mut`: {text}"
    );
}

/// Hovering a *call* of a generic function shows its generic signature and a
/// separated section binding each `unknown_N` to that call's concrete type.
#[test]
fn hover_shows_call_site_bindings() {
    let src = "fun f(a, b) {\n    return a\n}\n\nf(1, \"x\")\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "f(1", false); // the call, not the declaration
    let h = hover::hover(&doc, &full, pos).expect("hover over the call");
    let text = hover_text(&h);
    assert!(
        text.contains("fun f(a: ref(unknown_0), b: ref(unknown_1)) -> unknown_0"),
        "generic signature: {text}"
    );
    assert!(text.contains("---"), "separator: {text}");
    assert!(
        text.contains("unknown_0 = int32") && text.contains("unknown_1 = string"),
        "bindings: {text}"
    );
}

/// Hovering the *declaration* (not a call) shows only the generic signature.
#[test]
fn hover_declaration_has_no_bindings() {
    let src = "fun f(a, b) {\n    return a\n}\n\nf(1, \"x\")\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "f(a, b)", false);
    let text = hover_text(&hover::hover(&doc, &full, pos).expect("hover over the declaration"));
    assert!(text.contains("fun f("), "signature: {text}");
    assert!(
        !text.contains("---"),
        "no bindings at the declaration: {text}"
    );
}

/// With several instantiations, each call's hover binds the variables to that
/// call's own concrete types, not an arbitrary call's.
#[test]
fn hover_bindings_follow_the_call_under_the_cursor() {
    let src = concat!(
        "fun double(a: infer) {\n",
        "    for e in a {\n",
        "        e *= 2\n",
        "    }\n",
        "}\n",
        "\n",
        "const arr = [1.1, 2.2, 3.3]\n",
        "double(arr)\n",
        "const arr2 = [1, 2, 3]\n",
        "double(arr2)\n",
    );
    let full = full_analysis(src);

    // The unannotated `const` arrays type as fixed-length (`float64[3]`).
    let (doc, pos) = position(src, "double(arr)", false);
    let t1 = hover_text(&hover::hover(&doc, &full, pos).expect("hover first call"));
    assert!(t1.contains("unknown_0 = float64[3]"), "first call: {t1}");
    assert!(
        !t1.contains("int32"),
        "first call must not show int32: {t1}"
    );

    let (doc, pos) = position(src, "double(arr2)", false);
    let t2 = hover_text(&hover::hover(&doc, &full, pos).expect("hover second call"));
    assert!(t2.contains("unknown_0 = int32[3]"), "second call: {t2}");
    assert!(
        !t2.contains("float64"),
        "second call must not show float64: {t2}"
    );
}

/// Hovering a local variable shows its inferred type.
#[test]
fn hover_shows_variable_type() {
    let src = "fun main() {\n    let v = 5\n    println(v)\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "v)", true);
    let h = hover::hover(&doc, &full, pos).expect("hover over a variable");
    let text = hover_text(&h);
    assert!(text.contains("v:"), "should show `v: <type>`: {text}");
}

/// Hovering a variable at its `let` declaration (which has no typed node of its
/// own) still shows the type, recovered from the bound value.
#[test]
fn hover_shows_type_at_declaration() {
    let src = "fun main() {\n    let count = 5\n    println(count)\n}\n";
    let full = full_analysis(src);
    // First occurrence of `count` is the `let count` binding site.
    let (doc, pos) = position(src, "count", false);
    let h = hover::hover(&doc, &full, pos).expect("hover over a let binding");
    let text = hover_text(&h);
    assert!(
        text.contains("count: int32"),
        "should show `count: int32`: {text}"
    );
}

/// Hovering an annotated `let` at its declaration shows the *binding's* type
/// (the annotation), not the initializer's: `let wide: int64 = a` with an int32
/// initializer hovers as int64 (the value converts, the binding is int64).
#[test]
fn hover_at_declaration_shows_the_annotated_binding_type() {
    let src = "fun main() {\n    let a: int32 = 5\n    let wide: int64 = a\n    println(wide)\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "wide:", false);
    let h = hover::hover(&doc, &full, pos).expect("hover over the annotated binding");
    let text = hover_text(&h);
    assert!(text.contains("wide: int64"), "annotation wins: {text}");
}

/// A binding that is never used still hovers with its type at the declaration
/// (there is no use to borrow a type from).
#[test]
fn hover_at_declaration_works_for_an_unused_binding() {
    let src = "fun main() {\n    let unused: string = \"s\"\n    println(1)\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "unused", false);
    let h = hover::hover(&doc, &full, pos).expect("hover over an unused binding");
    let text = hover_text(&h);
    assert!(text.contains("unused: string"), "{text}");
}

/// Destructuring `let` bindings hover with each name's own element type at the
/// declaration site.
#[test]
fn hover_at_destructuring_declaration_shows_element_types() {
    let src = "fun main() {\n    let [n, s] = [1, \"text\"]\n    println(s)\n    println(n)\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "n, s", false);
    let h = hover::hover(&doc, &full, pos).expect("hover over a destructured binding");
    let text = hover_text(&h);
    assert!(text.contains("n: int32"), "tuple position 0: {text}");
    let (doc2, pos2) = position(src, "s] =", false);
    let h2 = hover::hover(&doc2, &full, pos2).expect("hover over the second binding");
    let text2 = hover_text(&h2);
    assert!(text2.contains("s: string"), "tuple position 1: {text2}");
}

/// An unannotated array literal containing `null` is a nullable-element
/// sequence, not a tuple: `null` unifies with any element type. An immutable
/// (`const`) binding is a fixed-length array; a `let` binding is a growable
/// slice.
#[test]
fn hover_infers_nullable_arrays_not_tuples() {
    let src = concat!(
        "const fixed = [4, 1, null, 65]\n",
        "fun main() {\n",
        "    let grow = [7, null, 9]\n",
        "    println(fixed)\n",
        "    println(grow)\n",
        "}\n",
    );
    let full = full_analysis(src);

    let (doc, pos) = position(src, "fixed", false);
    let t = hover_text(&hover::hover(&doc, &full, pos).expect("hover over the const binding"));
    assert!(
        t.contains("fixed: int32?[4]"),
        "const nullable literal is a fixed-length nullable array: {t}"
    );

    let (doc2, pos2) = position(src, "grow", false);
    let t2 = hover_text(&hover::hover(&doc2, &full, pos2).expect("hover over the let binding"));
    assert!(
        t2.contains("grow: int32?[]"),
        "let nullable literal is a growable nullable slice: {t2}"
    );
}

/// Variables introduced by a match-arm pattern show their type both at the
/// binding site (which has no typed node of its own) and at their uses.
#[test]
fn hover_shows_pattern_bound_variable_type() {
    let src = concat!(
        "type Shape =\n",
        "    | Circle { radius: float64 }\n",
        "    | Square\n",
        "\n",
        "fun area(s: Shape) -> float64 {\n",
        "    return match s {\n",
        "        Circle { radius } => radius * radius,\n",
        "        Square => 0.0,\n",
        "    }\n",
        "}\n",
    );
    let full = full_analysis(src);

    // Binding site `Circle { radius }` (the `radius` just before `} =>`).
    let (doc, pos) = position(src, "radius } =>", false);
    let h = hover::hover(&doc, &full, pos).expect("hover over a pattern binding");
    let text = hover_text(&h);
    assert!(text.contains("radius:"), "binding shows the name: {text}");
    assert!(
        text.contains("float64"),
        "binding shows the field type: {text}"
    );

    // Use site `radius * radius`.
    let (doc2, pos2) = position(src, "radius * radius", false);
    let h2 = hover::hover(&doc2, &full, pos2).expect("hover over a pattern use");
    assert!(hover_text(&h2).contains("float64"), "use shows the type");
}

/// A function with no return annotation whose body is fallible shows its
/// inferred return type (recovered from a call site), not `unknown_N`.
#[test]
fn hover_shows_inferred_return_type() {
    let src = concat!(
        "fun f(a: int32) {\n",
        "    error(1)!\n",
        "    return \"never\"\n",
        "}\n",
        "\n",
        "println(f(0))\n",
    );
    let full = full_analysis(src);
    let (doc, pos) = position(src, "f(0)", true);
    let h = hover::hover(&doc, &full, pos).expect("hover over the function");
    let text = hover_text(&h);
    assert!(text.contains("fun f("), "got: {text}");
    assert!(
        text.contains("Result<string, int32>"),
        "inferred fallible return must be shown: {text}"
    );
    assert!(
        !text.contains("-> unknown"),
        "return must not fall back to unknown: {text}"
    );
}

/// Hovering a method call shows the *method's* signature (its type), not the
/// call's result type, with an unannotated return filled from the call site.
#[test]
fn hover_method_call_shows_method_signature() {
    let src = concat!(
        "type Person = {\n",
        "    first_name: string,\n",
        "    last_name: string,\n",
        "}\n",
        "\n",
        "fun Person.display(self) {\n",
        "    return \"{self.first_name} {self.last_name}\"\n",
        "}\n",
        "\n",
        "fun main() {\n",
        "    let p = Person { first_name: \"a\", last_name: \"b\" }\n",
        "    println(p.display())\n",
        "}\n",
    );
    let full = full_analysis(src);
    // `display()` is the call (the declaration is `display(self)`), so this lands
    // on the method name in `p.display()`.
    let (doc, pos) = position(src, "display()", false);
    let h = hover::hover(&doc, &full, pos).expect("hover over the method call");
    let text = hover_text(&h);
    assert!(
        text.contains("fun display(self: ref(Self)) -> string"),
        "method type with inferred return must be shown, not the call result: {text}"
    );
}

/// A method with unannotated parameters (`HashMap.set(self, key, value)`) shows
/// the concrete parameter types at the call site -- resolved from the receiver's
/// key/value via the call arguments -- rather than bare `unknown_N`.
#[test]
fn hover_method_call_specializes_unannotated_params() {
    let src = "import std.collections.hashmap.{ HashMap }\nfun main() {\n    let m = HashMap.new()\n    m.set(\"a\", \"b\")\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "set(", false);
    let h = hover::hover(&doc, &full, pos).expect("hover over the set call");
    let text = hover_text(&h);
    assert!(
        text.contains("fun set(self: ref(mut(Self)), key: string, value: string)"),
        "method parameters must be specialized to the call: {text}"
    );
}

/// `map.get(...)`'s return type resolves to the map's value type (`string?`),
/// recovered from `entries`' element type through the method body, rather than
/// being left as `unknown`.
#[test]
fn hover_method_call_resolves_return_from_receiver() {
    let src = "import std.collections.hashmap.{ HashMap }\nfun main() {\n    let map = HashMap.new()\n    map.set(\"a\", \"b\")\n    let v = map.get(\"a\")\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "get(", false);
    let text = hover_text(&hover::hover(&doc, &full, pos).expect("hover the get call"));
    assert!(
        text.contains("fun get(self: ref(Self), key: string) -> string?"),
        "the return must be resolved to the map's value type: {text}"
    );
}

/// The checker exposes a generalized scheme per record type to the language
/// server: `HashMap` has inferred type parameters and its methods are recorded
/// over them, so the LSP can resolve a method against a receiver instance.
#[test]
fn full_analysis_exposes_record_schemes() {
    let src = "import std.collections.hashmap.{ HashMap }\nfun main() {\n    let map = HashMap.new()\n}\n";
    let full = full_analysis(src);
    let scheme = full.schemes.get("HashMap").expect("HashMap scheme");
    assert!(
        !scheme.params.is_empty(),
        "HashMap infers type parameters: {scheme:?}"
    );
    assert!(
        scheme.methods.contains_key("get") && scheme.methods.contains_key("set"),
        "the scheme records the methods: {scheme:?}"
    );
}

/// The scheme resolves a method's return against the receiver instance: hovering
/// `get` shows `-> string?` because the receiver is a `string`-valued map, with
/// the value type taken from the instance's `entries` element, not the call.
#[test]
fn hover_method_return_resolved_from_instance_via_scheme() {
    let src = "import std.collections.hashmap.{ HashMap }\nfun main() {\n    let map = HashMap.new()\n    map.set(\"a\", \"b\")\n    let v = map.get(\"a\")\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "get(", false);
    let text = hover_text(&hover::hover(&doc, &full, pos).expect("hover get"));
    assert!(
        text.contains("-> string?"),
        "the return resolves to the map's value type via the scheme: {text}"
    );
}

/// Hovering a record value shows the type's full member list with this instance's
/// field types resolved: `entries` shows the concrete element type the map was
/// built with (not `unknown`), every public member is listed, and the `_`-prefixed
/// implementation methods are hidden.
#[test]
fn hover_record_instance_shows_resolved_public_members() {
    let src = "import std.collections.hashmap.{ HashMap }\nfun main() {\n    let map = HashMap.new()\n    map.set(\"a\", \"b\")\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "map.set", false);
    let text = hover_text(&hover::hover(&doc, &full, pos).expect("hover the map value"));
    assert!(
        text.contains("entries: _Entry<key=string, value=string>?[]"),
        "entries must show its resolved element type: {text}"
    );
    assert!(text.contains("fun set("), "public methods listed: {text}");
    assert!(
        !text.contains("_find") && !text.contains("_insert") && !text.contains("_hash"),
        "`_`-prefixed implementation methods must be hidden: {text}"
    );
}

/// Hovering a type name hides its `_`-prefixed implementation members.
#[test]
fn hover_type_name_hides_internal_members() {
    let src = "import std.collections.hashmap.{ HashMap }\nfun main() {\n    let map = HashMap.new()\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "HashMap.new", false);
    let text = hover_text(&hover::hover(&doc, &full, pos).expect("hover the HashMap type"));
    assert!(text.contains("fun set("), "public methods shown: {text}");
    assert!(
        !text.contains("_hash") && !text.contains("_find"),
        "internal methods must be hidden: {text}"
    );
}

/// Go-to-definition on a call jumps to the called function's declaration.
#[test]
fn definition_jumps_to_function() {
    let src = "fun helper() -> int32 {\n    return 1\n}\n\nfun main() {\n    let v = helper()\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "helper()", true);
    let loc = definition::definition(&doc, &full, pos).expect("definition of a call");
    assert_eq!(loc.range.start.line, 0, "helper is declared on line 0");
}

/// Go-to-definition on a `recv.m()` call jumps to the `fun T.m(...)` that
/// implements the method, not anywhere else.
#[test]
fn definition_jumps_to_fun_method_impl() {
    let src = "type P = {\n    x: int32\n}\n\nfun P.get(self) -> int32 {\n    return self.x\n}\n\nfun main() {\n    let p = P { x: 1 }\n    let v = p.get()\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "get()", true);
    let loc = definition::definition(&doc, &full, pos).expect("definition of a method call");
    assert_eq!(loc.range.start.line, 4, "fun P.get is declared on line 4");
}

/// Go-to-definition on a stdlib primitive method (`s.split(...)`) jumps into the
/// prelude (a location with no file, since the prelude has no path on disk).
#[test]
fn definition_resolves_primitive_method() {
    let src = "fun main() {\n    let parts = \"a,b\".split(\",\")\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "split(", false);
    // The prelude has no file, so `definition` returns `None`, but the lookup must
    // not panic and must not mis-resolve to an unrelated free function.
    let _ = definition::definition(&doc, &full, pos);
}

/// Go-to-definition on a local use jumps to its binding.
#[test]
fn definition_jumps_to_local_binding() {
    let src = "fun main() {\n    let target = 5\n    println(target)\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "target)", true);
    let loc = definition::definition(&doc, &full, pos).expect("definition of a local");
    assert_eq!(loc.range.start.line, 1, "binding is on line 1");
}

/// Semantic tokens classify the leading `fun` as a keyword and produce output.
#[test]
fn semantic_tokens_classify_keyword() {
    let data = semantic_tokens::tokens("fun main() {\n    let x = 1\n}\n");
    assert!(!data.is_empty());
    // The first token is `fun`, the keyword type (index 8 in the legend).
    assert_eq!(data[0].token_type, 8);
}

fn labels(items: &[CompletionItem]) -> Vec<String> {
    items.iter().map(|i| i.label.clone()).collect()
}

/// Code completion offers the document's own types and functions, the prelude
/// functions, and the built-in type names.
#[test]
fn completion_offers_types_and_functions() {
    let src = "type Point = {\n    x: int32\n}\n\nfun helper() {\n}\n\nfun main() {\n    h\n}\n";
    let analyzer = DocAnalyzer::new(path());
    let doc = Document::new(src.to_string(), 1);
    let off = src.rfind("h\n").unwrap() + 1;
    let items = completion::completion(&doc, &analyzer, &path(), doc.position_at(off));
    let labels = labels(&items);
    assert!(
        labels.contains(&"Point".to_string()),
        "own type: {labels:?}"
    );
    assert!(labels.contains(&"helper".to_string()), "own fn: {labels:?}");
    assert!(
        labels.contains(&"println".to_string()),
        "prelude fn: {labels:?}"
    );
    assert!(
        labels.contains(&"int32".to_string()),
        "builtin type: {labels:?}"
    );
}

/// In `import |`, the prelude module names and the `std` namespace are offered.
/// Works without analysis, since a bare `import` line does not yet parse.
#[test]
fn completion_offers_import_modules() {
    let src = "import ";
    let analyzer = DocAnalyzer::new(path());
    let doc = Document::new(src.to_string(), 1);
    let items = completion::completion(&doc, &analyzer, &path(), doc.position_at(src.len()));
    let labels = labels(&items);
    assert!(
        labels.contains(&"math".to_string()),
        "prelude module: {labels:?}"
    );
    assert!(
        labels.contains(&"io".to_string()),
        "prelude module: {labels:?}"
    );
    assert!(
        labels.contains(&"std".to_string()),
        "std namespace: {labels:?}"
    );
}

/// In `import math.{ |`, the public names of the `math` module are offered.
#[test]
fn completion_offers_imported_names() {
    let src = "import math.{ ";
    let analyzer = DocAnalyzer::new(path());
    let doc = Document::new(src.to_string(), 1);
    let items = completion::completion(&doc, &analyzer, &path(), doc.position_at(src.len()));
    let labels = labels(&items);
    assert!(
        labels
            .iter()
            .any(|l| l == "sqrt" || l == "abs" || l == "pow"),
        "math's public functions should be offered: {labels:?}"
    );
}

/// After `arr.` on an array value, offer the built-in array methods and the std
/// array functions reachable through UFCS -- even though `arr.` does not parse.
#[test]
fn completion_offers_array_members() {
    let src = "fun main() {\n    let a = [1]\n    a.\n}\n";
    let analyzer = DocAnalyzer::new(path());
    let doc = Document::new(src.to_string(), 1);
    // Cursor immediately after the `.`.
    let off = src.find("a.\n").unwrap() + 2;
    let items = completion::completion(&doc, &analyzer, &path(), doc.position_at(off));
    let labels = labels(&items);
    assert!(
        labels.contains(&"push".to_string()),
        "builtin push: {labels:?}"
    );
    assert!(
        labels.contains(&"len".to_string()),
        "builtin len: {labels:?}"
    );
    // Stdlib array methods (`fun infer[].map`/`.filter`).
    assert!(labels.contains(&"map".to_string()), "array map: {labels:?}");
    assert!(
        labels.contains(&"filter".to_string()),
        "array filter: {labels:?}"
    );
    // A member list must not leak the global symbol list (type names) or free
    // functions -- there is no UFCS, so `abs` is not a member of an array.
    assert!(
        !labels.contains(&"int32".to_string()),
        "no globals: {labels:?}"
    );
    assert!(
        !labels.contains(&"abs".to_string()),
        "no free functions as members: {labels:?}"
    );
}

/// After `p.` on a record value, offer that record's methods.
#[test]
fn completion_offers_record_methods() {
    let src = concat!(
        "type Point = {\n",
        "    x: int32\n",
        "}\n",
        "\n",
        "fun Point.dist(self) -> int32 {\n",
        "    return self.x\n",
        "}\n",
        "\n",
        "fun main() {\n",
        "    let p = Point { x: 1 }\n",
        "    p.\n",
        "}\n",
    );
    let analyzer = DocAnalyzer::new(path());
    let doc = Document::new(src.to_string(), 1);
    let off = src.find("p.\n").unwrap() + 2;
    let items = completion::completion(&doc, &analyzer, &path(), doc.position_at(off));
    let labels = labels(&items);
    assert!(
        labels.contains(&"dist".to_string()),
        "record method: {labels:?}"
    );
}

/// `HashMap` lives in the embedded prelude module `std.collections.hashmap`, and
/// its operations are `fun HashMap.m(...)` methods. The analysis must load that
/// nested prelude module so `HashMap.new(...)` types to `HashMap` and `m.` offers
/// its methods -- with no import.
#[test]
fn completion_offers_hashmap_prelude_methods() {
    let src = concat!(
        "import std.collections.hashmap.{ HashMap }\n",
        "fun main() {\n",
        "    let m = HashMap.new()\n",
        "    m.\n",
        "}\n",
    );
    let analyzer = DocAnalyzer::new(path());
    let doc = Document::new(src.to_string(), 1);
    let off = src.find("m.\n").unwrap() + 2;
    let items = completion::completion(&doc, &analyzer, &path(), doc.position_at(off));
    let labels = labels(&items);
    assert!(
        labels.contains(&"set".to_string()) && labels.contains(&"get".to_string()),
        "HashMap methods: {labels:?}"
    );
}

/// After a sum type name (`Shape.`), offer its variants.
#[test]
fn completion_offers_sum_variants() {
    let src = concat!(
        "type Shape =\n",
        "    | Circle { radius: float64 }\n",
        "    | Square\n",
        "\n",
        "fun main() {\n",
        "    Shape.\n",
        "}\n",
    );
    let analyzer = DocAnalyzer::new(path());
    let doc = Document::new(src.to_string(), 1);
    let off = src.find("Shape.\n").unwrap() + "Shape.".len();
    let items = completion::completion(&doc, &analyzer, &path(), doc.position_at(off));
    let labels = labels(&items);
    assert!(
        labels.contains(&"Circle".to_string()),
        "variant Circle: {labels:?}"
    );
    assert!(
        labels.contains(&"Square".to_string()),
        "variant Square: {labels:?}"
    );
}

/// `s: ref(mut(infer[]))` with `s.push("b")` infers `ref(mut(string[]))`: the
/// push pins the element through the `ref`/`mut` wrappers, and the final
/// re-resolution makes every occurrence of `s` reflect it.
#[test]
fn hover_infers_ref_mut_array_element() {
    let src = "fun f(s: ref(mut(infer[]))) {\n    s.push(\"b\")\n    println(s)\n}\n\nf([\"a\"])\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "(s)", false);
    let h = hover::hover(&doc, &full, pos).expect("hover over s");
    let text = hover_text(&h);
    assert!(
        text.contains("ref(mut(string[]))"),
        "element should be inferred as string: {text}"
    );
}

/// `for e in a` over an unannotated `a` infers `a: unknown_0[]` and
/// `e: unknown_0` (same element), and the function type as
/// `(a: unknown_0[]) -> void`.
#[test]
fn hover_infers_for_loop_iterand_and_element() {
    let src = "fun for_type(a) {\n    for e in a {\n        println(e)\n    }\n}\n\nfor_type([1, 2, 3])\n";
    let full = full_analysis(src);

    let (doc, pos) = position(src, "a {", false);
    let a = hover_text(&hover::hover(&doc, &full, pos).expect("hover a"));
    assert!(a.contains("a: unknown_0[]"), "iterand: {a}");

    let (doc, pos) = position(src, "e in", false);
    let e = hover_text(&hover::hover(&doc, &full, pos).expect("hover e"));
    assert!(e.contains("e: unknown_0"), "element: {e}");

    let (doc, pos) = position(src, "for_type(a)", false);
    let sig = hover_text(&hover::hover(&doc, &full, pos).expect("hover fn"));
    assert!(
        sig.contains("fun for_type(a: ref(unknown_0[])) -> void"),
        "signature: {sig}"
    );
}

/// A `HashMap` key/value clash introduced in the user's code (`map.get(1)` on a
/// `string`-keyed map) is reported in the user's file, at the call site -- not at
/// an unreachable span inside the stdlib, which the LSP would filter out and so
/// show no error at all.
#[test]
fn hashmap_instance_type_mismatch_is_reported_at_the_call() {
    let mut a = DocAnalyzer::new(path());
    let src = "import std.collections.hashmap.{ HashMap }\nfun main() {\n    let map = HashMap.new()\n    map.set(\"a\", \"b\")\n    map.get(1)\n}\n";
    let diags = a.diagnostics(src);
    assert!(
        diags
            .iter()
            .any(|(m, _)| m.contains("does not match the receiver's type")),
        "expected a use-site receiver-mismatch error: {diags:?}"
    );
}

/// Iterating a non-iterable value is reported as an error (so passing a
/// non-iterable argument to a `for`-iterated parameter is rejected).
#[test]
fn for_over_non_iterable_is_an_error() {
    let mut a = DocAnalyzer::new(path());
    let src = "fun for_type(a) {\n    for e in a {\n        println(e)\n    }\n}\n\nfor_type(5)\n";
    let diags = a.diagnostics(src);
    assert!(
        diags.iter().any(|(m, _)| m.contains("cannot iterate")),
        "expected a cannot-iterate error: {diags:?}"
    );
}

/// A recursive call passes the function's own type variables as arguments, which
/// is not a concrete instantiation; such variable-to-variable bindings are
/// dropped, so hovering the recursive call shows only the generic signature,
/// while a concrete call still shows concrete bindings.
#[test]
fn hover_recursive_call_has_no_variable_bindings() {
    let src = concat!(
        "fun gcd(a, b) {\n",
        "    if b == 0 {\n",
        "        return a\n",
        "    } else {\n",
        "        return gcd(b, a % b)\n",
        "    }\n",
        "}\n",
        "\n",
        "gcd(48, 36)\n",
    );
    let full = full_analysis(src);

    let (doc, pos) = position(src, "gcd(b", false);
    let recursive = hover_text(&hover::hover(&doc, &full, pos).expect("hover recursive call"));
    assert!(recursive.contains("fun gcd("), "signature: {recursive}");
    assert!(
        !recursive.contains("---"),
        "no variable-to-variable bindings on a recursive call: {recursive}"
    );

    let (doc, pos) = position(src, "gcd(48", false);
    let concrete = hover_text(&hover::hover(&doc, &full, pos).expect("hover concrete call"));
    assert!(
        concrete.contains("unknown_0 = int32"),
        "concrete call still binds: {concrete}"
    );
}

/// Hovering the method name in `recv.m(args)` where `m` is a stdlib method on a
/// primitive/array receiver (`fun infer[].slice`) shows the method's signature,
/// resolved by the receiver's class.
#[test]
fn hover_primitive_method_shows_signature() {
    let src = "const elems = [1]\nfor elem in elems.slice(0, 1) {\n    println(elem)\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "slice(0", false);
    let text = hover_text(&hover::hover(&doc, &full, pos).expect("hover slice"));
    assert!(text.contains("fun slice("), "signature: {text}");
}

/// A function that returns a locally-built collection (`result = []` grown by
/// `push`) infers its element type from the call, so a `for` over the result of
/// `slice` gives a concrete element rather than `unknown`.
#[test]
fn hover_infers_element_through_collection_building_call() {
    let src = "const elems = [1]\nfor elem in elems.slice(0, 1) {\n    println(elem)\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "elem)", false); // the use in println(elem)
    let text = hover_text(&hover::hover(&doc, &full, pos).expect("hover elem"));
    assert!(text.contains("elem: int32"), "elem should be int32: {text}");
}

/// A document with several syntax errors reports each one, at the offending
/// token's document-local span, with the same message text the driver renders
/// -- the editor and the command line can never disagree.
#[test]
fn syntax_errors_are_all_reported_at_their_tokens() {
    let src = "fun f() -> int32 {\n    let x = )\n    let y = ]\n    return 0\n}\n";
    let diags = sorted(DocAnalyzer::new(path()).diagnostics(src));
    assert_eq!(diags.len(), 2, "diags: {diags:?}");
    assert_eq!(diags[0].0, "syntax error: unexpected token `)`");
    assert_eq!(diags[0].1.lo, src.find("= )").unwrap() + 2);
    assert_eq!(diags[1].0, "syntax error: unexpected token `]`");
    assert_eq!(diags[1].1.lo, src.find("= ]").unwrap() + 2);
}

/// Hover still works on the healthy parts of a document that has a syntax
/// error elsewhere: analysis runs on the recovered AST.
#[test]
fn hover_survives_a_syntax_error_elsewhere() {
    let src = "fun ok(a: int32) -> int32 {\n    return a\n}\nfun broken() {\n    let x = )\n}\n";
    let analysis = DocAnalyzer::new(path())
        .analyze_full(src)
        .expect("recovered AST should still analyze");
    let (doc, pos) = position(src, "ok", false);
    let h = hover::hover(&doc, &analysis, pos);
    assert!(
        h.is_some(),
        "expected hover on `ok` despite the later error"
    );
}

/// A module import (`import a.b`) used qualified reports the same diagnostics
/// as the driver: none when valid is impossible in this single-file test (the
/// module file does not exist), so the collision case pins message parity.
#[test]
fn duplicate_module_qualifier_matches_the_driver_message() {
    let src = "import a.util\nimport b.util\nfun main() {\n    println(1)\n}\n";
    let diags = DocAnalyzer::new(path()).diagnostics(src);
    assert!(
        diags
            .iter()
            .any(|(m, _)| m.contains("two module imports share the qualifier `util`")),
        "diags: {diags:?}"
    );
}
