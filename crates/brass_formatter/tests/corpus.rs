//! Corpus test: format every `.cz` file in the repository and check the three
//! properties a formatter must not break:
//!   1. the output parses;
//!   2. the output's AST equals the input's (spans aside) -- formatting never
//!      changes what the program means;
//!   3. formatting is idempotent.
//!
//! Files that do not parse (parser-recovery fixtures) are skipped: the
//! formatter refuses those by design.

use std::fs;
use std::path::{Path, PathBuf};

fn collect_cz(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_cz(&path, out);
        } else if path.extension().is_some_and(|e| e == "cz") {
            out.push(path);
        }
    }
}

/// The AST debug output with every `Span { .. }` collapsed, so two parses of
/// differently laid-out sources compare structurally.
fn strip_spans(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut rest = s;
    while let Some(i) = rest.find("Span {") {
        out.push_str(&rest[..i]);
        out.push_str("Span");
        let after = &rest[i..];
        let j = after.find('}').expect("span debug always closes");
        rest = &after[j + 1..];
    }
    out.push_str(rest);
    out
}

#[test]
fn repo_sources_reformat_losslessly() {
    // Some corpus files nest expressions up to the parser's depth cap; the
    // printer's recursion (and the AST's derived Debug) need more than the
    // default 2 MiB test-thread stack in debug builds.
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(check_repo_sources)
        .expect("spawn corpus thread")
        .join()
        .expect("corpus thread panicked");
}

fn check_repo_sources() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut files = Vec::new();
    for dir in ["core", "examples", "e2e_tests"] {
        collect_cz(&root.join(dir), &mut files);
    }
    assert!(
        files.len() > 20,
        "corpus unexpectedly small: {} files",
        files.len()
    );
    let mut checked = 0;
    for path in files {
        let src = fs::read_to_string(&path).expect("read corpus file");
        let Ok(original) = brass_parser::parse(&src) else {
            continue; // recovery fixtures with intentional syntax errors
        };
        let formatted = brass_formatter::format_source(&src)
            .unwrap_or_else(|e| panic!("{}: format failed: {e:?}", path.display()));
        let reparsed = brass_parser::parse(&formatted).unwrap_or_else(|e| {
            panic!(
                "{}: formatted output failed to parse: {} at {:?}\n---\n{formatted}",
                path.display(),
                e.message,
                e.span
            )
        });
        assert_eq!(
            strip_spans(&format!("{original:?}")),
            strip_spans(&format!("{reparsed:?}")),
            "{}: formatting changed the AST\n---\n{formatted}",
            path.display()
        );
        let again = brass_formatter::format_source(&formatted)
            .unwrap_or_else(|e| panic!("{}: second format failed: {e:?}", path.display()));
        assert_eq!(
            formatted,
            again,
            "{}: formatting is not idempotent",
            path.display()
        );
        checked += 1;
    }
    assert!(checked > 20, "too few files checked: {checked}");
}
