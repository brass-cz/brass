//! The open buffer is an own root; imported bodies follow shared reachability.

use super::{DocAnalyzer, Document, completion, sorted};
use std::path::PathBuf;

struct Fixture(PathBuf);
impl Fixture {
    fn new(name: &str, library: &str) -> Self {
        let root =
            std::env::temp_dir().join(format!("brass-editor-items-{}-{name}", std::process::id()));
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(root.join("lib.cz"), library).unwrap();
        Self(root)
    }
    fn analyzer(&self, file: &str) -> DocAnalyzer {
        DocAnalyzer::new(self.0.join(file))
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn opening_a_dependency_checks_its_unused_bodies() {
    let library = "fun good() { return 7 }\nfun bad() -> int32 { return false }";
    let fixture = Fixture::new("open", library);
    let source = "import lib.{ good }\nlet x = good()";
    let mut entry = fixture.analyzer("main.cz");
    assert!(entry.diagnostics(source).is_empty());
    let full = entry.analyze_full(source);
    assert!(
        full.program.functions.contains_key("bad"),
        "declarations remain visible"
    );
    assert!(
        !full.function_returns.contains_key("bad"),
        "an unused imported body is not inferred"
    );
    let mut opened = fixture.analyzer("lib.cz");
    assert!(
        !opened.diagnostics(library).is_empty(),
        "opening makes every item own code"
    );
    drop(opened);
    assert!(
        entry.diagnostics(source).is_empty(),
        "other buffers never inherit the opened roots"
    );
}

#[test]
fn edits_grow_and_shrink_selection_without_reusing_stale_seeds() {
    let fixture = Fixture::new(
        "edits",
        "fun one() { return 1 }\nfun text() { return \"x\" }",
    );
    let mut analyzer = fixture.analyzer("main.cz");
    for (callee, bad) in [("one", false), ("text", true), ("one", false)] {
        let source =
            format!("import lib.{{ one, text }}\nfun unused() {{ let x: int32 = {callee}() }}");
        let got = sorted(analyzer.diagnostics(&source));
        assert_eq!(!got.is_empty(), bad, "{got:?}");
        assert_eq!(
            got,
            sorted(fixture.analyzer("main.cz").diagnostics(&source))
        );
        let full = analyzer.analyze_full(&source);
        assert!(full.function_returns.contains_key(callee));
        assert!(
            !full
                .function_returns
                .contains_key(if callee == "one" { "text" } else { "one" })
        );
    }
}

#[test]
fn dependency_member_edits_invalidate_negative_facts() {
    let initial = "type Choice = | A | B";
    let fixture = Fixture::new("members", initial);
    let source = "import lib.{ Choice }\nfun main() { let x: int32 = Choice.A.value() }";
    let mut analyzer = fixture.analyzer("main.cz");
    assert!(!analyzer.diagnostics(source).is_empty());
    std::fs::write(
        fixture.0.join("lib.cz"),
        format!("{initial}\nfun Choice.value(self) -> int32 {{ return 7 }}"),
    )
    .unwrap();
    assert!(analyzer.diagnostics(source).is_empty());
    std::fs::write(fixture.0.join("lib.cz"), initial).unwrap();
    assert!(!analyzer.diagnostics(source).is_empty());
}

#[test]
fn completion_keeps_declared_members_without_checking_their_bodies() {
    let fixture = Fixture::new(
        "completion",
        "type Choice = | A | B\nfun Choice.bad(self) -> int32 { return false }",
    );
    let source = "import lib.{ Choice }\nlet x = Choice.A\nx.";
    let analyzer = fixture.analyzer("main.cz");
    let doc = Document::new(source.to_string(), 1);
    let items = completion::completion(
        &doc,
        &analyzer,
        &fixture.0.join("main.cz"),
        doc.position_at(source.len()),
    );
    assert!(items.iter().any(|item| item.label == "bad"), "{items:?}");
}

#[test]
fn recovered_imported_body_does_not_hide_good_siblings() {
    let fixture = Fixture::new(
        "recovery",
        "fun good() { return 7 }\nfun bad() { let x =\nreturn 1\n}",
    );
    let source = "import lib.{ good }\nlet x: int32 = good()";
    assert!(fixture.analyzer("main.cz").diagnostics(source).is_empty());
    let full = fixture.analyzer("main.cz").analyze_full(source);
    assert!(full.program.functions.contains_key("good"));
    assert!(!full.function_returns.contains_key("bad"));
    // The same malformed body is always reported when its file is opened.
    let library = std::fs::read_to_string(fixture.0.join("lib.cz")).unwrap();
    assert!(!fixture.analyzer("lib.cz").diagnostics(&library).is_empty());
}

#[test]
fn entry_main_identity_tracks_the_open_buffer() {
    let fixture = Fixture::new(
        "entry-main",
        "fun main() {}
fun value() -> int32! { return 7 }",
    );
    let mut analyzer = fixture.analyzer("main.cz");
    // Reusing the analyzer must not promote the imported main after an edit.
    for has_main in [true, false, true] {
        let source = if has_main {
            "import lib
fun main() { println(lib.value()!) }"
        } else {
            "import lib
println(1)"
        };
        assert!(analyzer.diagnostics(source).is_empty());
        let full = analyzer.analyze_full(source);
        assert_eq!(full.program.entry_function().is_some(), has_main);
        if let Some(symbol) = full.program.entry_function() {
            assert_eq!(full.program.functions[symbol].module, ["main"]);
        }
    }
}
