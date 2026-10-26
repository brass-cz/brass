//! Execution-location policy and provenance across driver entry points.

mod support;

use std::io::Write;
use std::process::Stdio;

#[test]
fn only_execution_modes_build_location_tables() {
    let source = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../e2e_tests/call/implicit_location_unicode_crlf.cz"
    );
    for mode in [Some("check"), None, Some("--eager"), Some("repl")] {
        let output = support::brass_command(env!("CARGO_BIN_EXE_brass"))
            .args(mode)
            .arg(source)
            .env("BRASS_LOG", "brass::perf=debug")
            .env("BRASS_JIT_CACHE", "off")
            .output()
            .expect("run location fixture");
        assert!(output.status.success(), "{mode:?}: {output:?}");
        assert_eq!(
            output.stdout,
            if mode == Some("check") {
                &b""[..]
            } else {
                &b"4:23\n"[..]
            },
            "{mode:?}"
        );
        let log = String::from_utf8_lossy(&output.stderr);
        // The lazy executor owns one table; its checker must not build another.
        assert_eq!(
            log.matches("front/source-locations: total").count(),
            usize::from(mode != Some("check")),
            "{mode:?}: {log}"
        );
    }
}

#[test]
fn interactive_repl_keeps_locations_across_submissions() {
    let mut child = support::brass_command(env!("CARGO_BIN_EXE_brass"))
        .arg("repl")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn interactive REPL");
    child.stdin.take().unwrap().write_all(
        b"fun capture(loc: Location) { println(\"{loc.line}:{loc.col}\") }\ncapture()\ncapture()\n",
    ).unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{output:?}");
    // Each submitted statement is assembled after the retained definition.
    assert_eq!(output.stdout, b"3:1\n3:1\n");
    assert!(!String::from_utf8_lossy(&output.stderr).contains("error:"));
}
