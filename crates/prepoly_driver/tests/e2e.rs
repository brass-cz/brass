//! End-to-end tests for record-field and sum-variant features. Each `*.pp` under
//! `e2e_tests/` is run through the driver and checked against a sibling
//! expectation. Two expectation kinds are supported:
//!
//! - `*.out`: the program must run successfully and its stdout must match the file
//!   byte-for-byte (the common success case).
//! - `*.err`: the program must *fail* (non-zero exit) and its stderr must contain
//!   the file's trimmed contents as a substring. This pins the diagnostics for
//!   programs that must be rejected -- e.g. the slice-element and anonymous-struct
//!   type holes a value would otherwise corrupt the unboxed back end through.
//!
//! Cases are grouped by subsystem (`field/`, `variant/`, `types/`, `structure/`,
//! `references/`, ...). `concurrency/` cases use `spawn`/`with`, which only the JIT
//! back end runs, so that directory is skipped when the `jit` feature is off (the
//! interpreter rejects concurrency at runtime).

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn e2e_root() -> PathBuf {
    // The driver manifest lives at crates/prepoly_driver; the repo root is two up.
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../e2e_tests")
}

/// Every `*.pp` under `dir`, recursively, in sorted order (so failures are stable).
/// `concurrency/`, `net/`, and `process/` are skipped without the `jit`
/// feature: those cases need real threads, sockets, and child processes that
/// only the JIT back end provides.
fn collect_cases(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .map(|e| e.unwrap().path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            if !cfg!(feature = "jit")
                && path
                    .file_name()
                    .is_some_and(|n| n == "concurrency" || n == "net" || n == "process")
            {
                continue;
            }
            collect_cases(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "pp") {
            out.push(path);
        }
    }
}

/// The in-repo `libraries/` directory, whose modules are reachable as
/// packages (`process=<libraries>` makes `import process.{ .. }` resolve).
fn libraries_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../libraries")
}

/// Run a case, exposing `libraries/` as packages so a case may import a
/// library (`process/` does). Cases that import nothing from there are
/// unaffected.
fn run_case(bin: &str, pp: &Path) -> std::process::Output {
    Command::new(bin)
        .arg(pp)
        .env(
            "PREPOLY_PACKAGES",
            format!("process={}", libraries_root().display()),
        )
        .output()
        .expect("spawn prepoly")
}

/// Run a success case: the program must exit zero and print exactly `expected`.
fn check_success(bin: &str, pp: &Path, expected: &str) {
    let out = run_case(bin, pp);
    assert!(
        out.status.success(),
        "{} failed to run (status {:?})\nstderr:\n{}",
        pp.display(),
        out.status.code(),
        String::from_utf8_lossy(&out.stderr),
    );
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        expected,
        "{} produced unexpected stdout",
        pp.display(),
    );
}

/// Run an error case: the program must exit non-zero and its stderr must contain
/// every line of `expected` (trimmed) as a substring, so the diagnostic is pinned
/// without coupling to the absolute source path the driver prints.
fn check_error(bin: &str, pp: &Path, expected: &str) {
    let out = run_case(bin, pp);
    assert!(
        !out.status.success(),
        "{} was expected to fail but succeeded\nstdout:\n{}",
        pp.display(),
        String::from_utf8_lossy(&out.stdout),
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    for needle in expected.lines().map(str::trim).filter(|l| !l.is_empty()) {
        assert!(
            stderr.contains(needle),
            "{} stderr did not contain `{needle}`\nstderr:\n{stderr}",
            pp.display(),
        );
    }
}

#[test]
fn e2e_cases_produce_expected_output() {
    let bin = env!("CARGO_BIN_EXE_prepoly");
    // The `process/` cases import the process library, whose native half is a
    // plugin; install it as `libraries/build.sh` would. Those cases only run
    // with the JIT back end (the interpreter has no file I/O for the pipes).
    #[cfg(feature = "jit")]
    prepoly_plugin_host::fixture::install_plugin(
        "prepoly_lib_process",
        "process",
        &libraries_root().join("process"),
    );
    let root = e2e_root();
    let mut cases = Vec::new();
    collect_cases(&root, &mut cases);
    assert!(
        !cases.is_empty(),
        "no e2e `.pp` cases found under {}",
        root.display()
    );

    for pp in &cases {
        match (
            fs::read_to_string(pp.with_extension("out")).ok(),
            fs::read_to_string(pp.with_extension("err")).ok(),
        ) {
            (Some(expected), None) => check_success(bin, pp, &expected),
            (None, Some(expected)) => check_error(bin, pp, &expected),
            (Some(_), Some(_)) => {
                panic!("{} has both a .out and a .err expectation", pp.display())
            }
            (None, None) => panic!("missing .out/.err expectation for {}", pp.display()),
        }
    }
}

/// The interpreter's call-depth guard must fire before the host stack
/// overflows: runaway recursion through `prepoly repl` ends in the guard's
/// clean error, not a process abort. (The JIT intentionally uses the native
/// stack, so only the interpreter path is pinned here.)
#[test]
fn repl_deep_recursion_hits_the_depth_guard() {
    let bin = env!("CARGO_BIN_EXE_prepoly");
    let pp = Path::new(env!("CARGO_TARGET_TMPDIR")).join("repl_deep_recursion.pp");
    fs::write(
        &pp,
        "fun f(n: int64) -> int64 {\n    if n == 0 { return 0 }\n    return f(n - 1)\n}\nprintln(f(20000))\n",
    )
    .expect("write recursion case");
    let out = Command::new(bin)
        .arg("repl")
        .arg(&pp)
        .output()
        .expect("spawn prepoly");
    assert!(
        !out.status.success(),
        "deep recursion was expected to fail cleanly\nstdout:\n{}",
        String::from_utf8_lossy(&out.stdout),
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("call stack depth exceeded"),
        "stderr did not contain the depth-guard error:\n{stderr}"
    );
}
