//! End-to-end tests over the crate's analysis and feature layers, exercised
//! through the same public entry points the LSP handlers use.

use std::path::PathBuf;

use prepoly_lexer::Span;

use crate::analysis::{DocAnalyzer, FullAnalysis};
use crate::document::Document;
use crate::features::{definition, hover, semantic_tokens};
use tower_lsp_server::ls_types::{HoverContents, Position};

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

/// Hovering a function whose parameter and return are unannotated shows them as
/// numbered `unknown_N`, the contract for an inference-open function type. The
/// function is never called, so no concrete return type can be recovered.
#[test]
fn hover_shows_unknown_numbered_signature() {
    let src = "fun id(x) {\n    return x\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "id(x)", false);
    let h = hover::hover(&doc, &full, pos).expect("hover over the function name");
    let text = hover_text(&h);
    assert!(text.contains("fun id("), "got: {text}");
    assert!(
        text.contains("unknown_0"),
        "param should be unknown_0: {text}"
    );
    assert!(
        text.contains("unknown_1"),
        "return should be unknown_1: {text}"
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
        text.contains("count:"),
        "should show `count: <type>`: {text}"
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

/// Go-to-definition on a call jumps to the called function's declaration.
#[test]
fn definition_jumps_to_function() {
    let src = "fun helper() -> int32 {\n    return 1\n}\n\nfun main() {\n    let v = helper()\n}\n";
    let full = full_analysis(src);
    let (doc, pos) = position(src, "helper()", true);
    let loc = definition::definition(&doc, &full, pos).expect("definition of a call");
    assert_eq!(loc.range.start.line, 0, "helper is declared on line 0");
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
