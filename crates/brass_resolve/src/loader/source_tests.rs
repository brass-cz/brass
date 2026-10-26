use super::SourceMap;
use std::sync::Arc;

#[test]
fn coordinates_cover_source_boundaries_and_plugin_text() {
    let mut sources = SourceMap::default();
    let core = "a\r\n\u{1f600}\t\n";
    let core_base = sources.add(None, "<core/test>".into(), core.into());
    let empty = sources.add(None, "<repl>".into(), String::new());
    let plugin_text = "\u{e9}\rx\ny";
    let plugin = sources.add_plugin(
        "missing.so".into(),
        vec!["test".into()],
        "<plugin:missing.so>".into(),
        plugin_text.into(),
    );
    // EOF belongs to the preceding entry; the next byte belongs to the next
    // source even when that source is empty.
    assert_eq!(empty, core_base + core.len() + 1);
    assert_eq!(plugin, empty + 1);
    for (base, text, label) in [
        (core_base, core, "<core/test>"),
        (empty, "", "<repl>"),
        (plugin, plugin_text, "<plugin:missing.so>"),
    ] {
        for local in 0..=text.len() {
            let located = sources.locate(base + local).expect("source offset");
            assert_eq!(located.label, label);
            assert_eq!(located.local, local);
            assert_eq!(located.line_col(), brass_parser::line_col(text, local));
        }
    }
    assert!(sources.locate(plugin + plugin_text.len() + 1).is_none());
    assert!(sources.locate(usize::MAX).is_none());
    assert!(SourceMap::default().locate(0).is_none());
}

#[test]
fn snapshots_share_lazy_indexes_but_distinct_sources_do_not() {
    let mut sources = SourceMap::default();
    let base = sources.add(None, "buffer".into(), "a\nb".into());
    let mut snapshot = sources.clone();
    assert!(sources.entries[0].line_index.get().is_none());
    assert!(Arc::ptr_eq(
        &sources.entries[0].line_index,
        &snapshot.entries[0].line_index
    ));
    assert_eq!(snapshot.locate(base + 2).unwrap().line_col(), (2, 1));
    assert!(sources.entries[0].line_index.get().is_some());
    // A buffer revision is a new immutable source even when its label agrees.
    let revised = snapshot.add(None, "buffer".into(), "ab\nc".into());
    assert!(snapshot.entries[1].line_index.get().is_none());
    assert_eq!(snapshot.locate(revised + 2).unwrap().line_col(), (1, 3));
    assert_eq!(sources.locate(base + 2).unwrap().line_col(), (2, 1));
}
