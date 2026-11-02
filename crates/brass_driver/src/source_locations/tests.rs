use super::call_site_locations;
use brass_hir::LoadedModule;
use brass_parser::Span;
use brass_resolve::{SearchPaths, SourceMap};

fn module(sources: &mut SourceMap, label: &str, src: &str) -> (usize, LoadedModule) {
    let base = sources.add(None, label.into(), src.into());
    let ast = brass_parser::parse_with_base(src, base).expect("parse fixture");
    (
        base,
        LoadedModule {
            source: None,
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        },
    )
}

#[test]
fn nested_return_locations_keep_full_spans_and_scalar_columns() {
    // The return and propagation share a span, while the wrapped call,
    // construction and nested call each retain their own extent.
    let text =
        "fun sample() {\r\n\t/* \u{1f600}e\u{301} */ return wrap(Box { value: inner() })!\r\n}\r\n";
    let mut sources = SourceMap::default();
    let (base, first) = module(&mut sources, "<buffer>", text);
    let (other_base, other) = module(
        &mut sources,
        "<buffer>",
        "\nfun other_body() {\nreturn other()\n}\n",
    );
    let table = call_site_locations(&[first, other], &sources, &SearchPaths::default());
    assert_eq!(table.len(), 5);
    for needle in [
        "wrap(Box { value: inner() })!",
        "wrap(Box { value: inner() })",
        "Box { value: inner() }",
        "inner()",
    ] {
        let start = text.find(needle).unwrap();
        let (line, col) = brass_parser::line_col(text, start);
        assert_eq!(
            table[&Span::new(base + start, base + start + needle.len())],
            ("<buffer>".into(), line as u32, col as u32)
        );
    }
    // Identical labels do not identify identical source texts.
    let start = other_base + "\nfun other_body() {\nreturn ".len();
    assert_eq!(
        table[&Span::new(start, start + "other()".len())],
        ("<buffer>".into(), 3, 8)
    );
}

#[test]
fn diagnostic_labels_stay_raw_and_secondary_locations_share_coordinates() {
    let mut sources = SourceMap::default();
    let text = "\r\n\t\u{1f600}e\u{301} call()";
    let base = sources.add(None, "./raw/../buffer.cz".into(), text.into());
    let offset = base + text.find("call").unwrap();
    let errors = vec![
        (
            format!("secondary \u{1f}{offset}\u{1f}"),
            Span::new(offset, offset + 4),
        ),
        ("unlocated".into(), Span::new(usize::MAX, usize::MAX)),
    ];
    assert_eq!(
        crate::render_errors(&errors, &sources),
        [
            "./raw/../buffer.cz:2:6: error: secondary ./raw/../buffer.cz:2:6",
            "error: unlocated",
        ]
    );
}

#[cfg(unix)]
#[test]
fn canonical_labels_are_scoped_to_one_table_build() {
    // Retargeting or removing a symlink between builds must not leave the
    // preceding build's canonical label in a process-global cache.
    let root = std::env::temp_dir().join(format!("brass-source-labels-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let target = root.join("real.cz");
    let alias = root.join("alias.cz");
    let text = "fun sample() {\nreturn first()\nreturn second()\n}\n";
    std::fs::write(&target, text).unwrap();
    std::os::unix::fs::symlink(&target, &alias).unwrap();
    let mut sources = SourceMap::default();
    let (_, loaded) = module(&mut sources, &alias.display().to_string(), text);
    let modules = [loaded];
    let search = SearchPaths {
        includes: vec![root.clone()],
        packages: fxhash::FxHashMap::from_iter([("fixture".into(), root.clone())]),
    };
    let first = call_site_locations(&modules, &sources, &search);
    assert!(
        first
            .values()
            .all(|(label, _, _)| label.ends_with("real.cz"))
    );
    std::fs::remove_file(&alias).unwrap();
    let second = call_site_locations(&modules, &sources, &search);
    assert!(
        second
            .values()
            .all(|(label, _, _)| label.ends_with("alias.cz"))
    );
    assert_eq!(first.len(), second.len());
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn embedded_and_missing_plugin_labels_preserve_their_spelling() {
    let mut sources = SourceMap::default();
    let mut modules = Vec::new();
    for label in ["<core/fixture>", "<plugin:not-a-real-location-library>"] {
        modules.push(module(&mut sources, label, "call()\n").1);
    }
    let table = call_site_locations(&modules, &sources, &SearchPaths::default());
    let mut labels: Vec<_> = table.values().map(|value| value.0.as_str()).collect();
    labels.sort();
    assert_eq!(
        labels,
        ["<core/fixture>", "<plugin:not-a-real-location-library>"]
    );
}
