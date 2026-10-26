use super::{DocAnalyzer, Document, diagnostics, path, sorted};

#[test]
fn incremental_warning_renders_shifted_scalar_secondary_locations() {
    let body = concat!(
        "fun mixed(c: int32) {\r\n",
        "\tif c == 1 { /* \u{1f600} */ error(\"a\")! }\r\n",
        "\telse if c == 2 { /* e\u{301} */ null! }\r\n",
        "\treturn 1\r\n",
        "}\r\n",
    );
    let mut analyzer = DocAnalyzer::new(path());
    for prefix in ["", "// \u{1f600}\r\n\r\n"] {
        let text = format!("{prefix}{body}");
        let raw = analyzer.diagnostics(&text);
        assert_eq!(
            sorted(raw.clone()),
            sorted(DocAnalyzer::new(path()).diagnostics(&text))
        );
        let published = diagnostics::to_lsp(&raw, &Document::new(text.clone(), 1));
        let warning = published
            .iter()
            .find(|d| d.message.contains("returns `Result"))
            .expect("mixed propagation warning");
        for needle in ["null!", "error(\"a\")!"] {
            // Message coordinates count scalars even though protocol ranges
            // continue to count UTF-16 and use their own newline rules.
            let (line, col) = brass_parser::line_col(&text, text.find(needle).unwrap());
            assert!(
                warning
                    .message
                    .contains(&format!("{}:{line}:{col}", path().display())),
                "{}",
                warning.message
            );
        }
        assert_eq!(
            warning.range.start.line,
            if prefix.is_empty() { 0 } else { 2 }
        );
    }
}
