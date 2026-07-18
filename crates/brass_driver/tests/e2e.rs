//! End-to-end tests for record-field and sum-variant features. Each `*.cz` under
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
    // The driver manifest lives at crates/brass_driver; the repo root is two up.
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../e2e_tests")
}

/// Every `*.cz` under `dir`, recursively, in sorted order (so failures are stable).
/// `concurrency/` is skipped without the `jit` feature (real threads need the
/// JIT back end), and so are the library directories (`net/`, `process/`,
/// `path/`, `fs/`) -- not because the interpreter cannot run them, but because
/// only the JIT configuration builds the native plugins the libraries import.
fn collect_cases(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .map(|e| e.unwrap().path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            if !cfg!(feature = "jit")
                && path.file_name().is_some_and(|n| {
                    n == "concurrency"
                        || n == "net"
                        || n == "process"
                        || n == "path"
                        || n == "fs"
                        || n == "http"
                        || n == "env"
                        || n == "hash"
                        || n == "regex"
                        || n == "semver"
                })
            {
                continue;
            }
            collect_cases(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "cz") {
            out.push(path);
        }
    }
}

/// The in-repo `std/` directory, bound to every case as the `std` package --
/// the same layout a distributed toolchain ships, so the cases exercise
/// exactly what users get.
fn std_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std")
}

/// The `BRASS_PACKAGES` value binding the in-repo standard library: the
/// package path is the directory CONTAINING `std/` (the repo root).
fn std_package_env() -> String {
    format!(
        "std={}",
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .display()
    )
}

/// The libraries whose native halves the suite builds: the cargo package
/// building each plugin, and the module/library name it is imported under.
#[cfg(feature = "jit")]
const NATIVE_LIBRARIES: &[(&str, &str)] = &[
    ("brass_lib_process", "process"),
    ("brass_lib_path", "path"),
    ("brass_lib_net", "net"),
    ("brass_lib_fs", "fs"),
    ("brass_lib_env", "env"),
    ("brass_lib_hash", "hash"),
    ("brass_lib_regex", "regex"),
];

/// Build each library's plugin and install it as `std/lib<name>.so`, where
/// `std/build.sh` puts it (a debug build here replaces a prior release
/// install). Installed once, before any case process runs, so no running
/// process has an older library mapped.
#[cfg(feature = "jit")]
fn install_library_plugins() {
    for (package, library) in NATIVE_LIBRARIES {
        brass_plugin_host::fixture::install_plugin(package, library, &std_root());
    }
}

/// Run a case with the `std` package bound, so a case may import a standard
/// library (`process/` and `path/` do). Cases that import nothing from there
/// are unaffected.
fn run_case(bin: &str, pp: &Path) -> std::process::Output {
    run_case_mode(bin, pp, false)
}

/// [`run_case`] with the check mode chosen: `eager` inserts `--eager` before
/// the file, forcing the whole-program check the annotated cases pin per
/// mode. (An interpreter-only build checks eagerly either way.)
fn run_case_mode(bin: &str, pp: &Path, eager: bool) -> std::process::Output {
    let mut cmd = Command::new(bin);
    cmd.env("BRASS_CACHE", "off");
    if eager {
        cmd.arg("--eager");
    }
    cmd.arg(pp)
        .env("BRASS_PACKAGES", std_package_env())
        .output()
        .expect("spawn brass")
}

/// Per-mode expectations parsed from a case's leading annotation lines:
///
/// ```text
/// // @lazy: pass
/// // @eager: fail
/// ```
///
/// Lazy checking ignores diagnostics in code execution never needs, so a
/// case can pass when run (the default, lazy) yet fail its whole-program
/// check (`--eager`). An annotated case carries BOTH a `.out` (the passing
/// mode's exact stdout) and a `.err` (the failing mode's diagnostic
/// substring) and runs in both modes; unannotated cases keep the
/// single-expectation behavior. The grammar is strict -- a typo must fail
/// the suite, not silently skip an expectation.
fn mode_expectations(src: &str) -> Option<(bool, bool)> {
    let mut lazy = None;
    let mut eager = None;
    for line in src.lines() {
        let Some(rest) = line.strip_prefix("// @") else {
            if line.starts_with("//") || line.trim().is_empty() {
                continue;
            }
            break;
        };
        let (mode, value) = rest
            .split_once(':')
            .unwrap_or_else(|| panic!("malformed mode annotation `{line}`"));
        let passes = match value.trim() {
            "pass" => true,
            "fail" => false,
            other => panic!("mode annotation value must be `pass` or `fail`, got `{other}`"),
        };
        match mode.trim() {
            "lazy" => lazy = Some(passes),
            "eager" => eager = Some(passes),
            other => panic!("unknown mode annotation `@{other}`"),
        }
    }
    match (lazy, eager) {
        (None, None) => None,
        (Some(l), Some(e)) => Some((l, e)),
        _ => panic!("a case with mode annotations must specify both @lazy and @eager"),
    }
}

/// Run a success case: the program must exit zero and print exactly `expected`.
fn check_success(bin: &str, pp: &Path, expected: &str) {
    check_success_mode(bin, pp, expected, false)
}

fn check_success_mode(bin: &str, pp: &Path, expected: &str, eager: bool) {
    let out = run_case_mode(bin, pp, eager);
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
    check_error_mode(bin, pp, expected, false)
}

fn check_error_mode(bin: &str, pp: &Path, expected: &str, eager: bool) {
    let out = run_case_mode(bin, pp, eager);
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
    let bin = env!("CARGO_BIN_EXE_brass");
    // The `process/` and `path/` cases import libraries whose native halves
    // are plugins; build them into `std/` as `std/build.sh` would. Those cases only run with the JIT back end (the interpreter has
    // no file I/O for the pipes, and only this configuration builds the
    // plugins).
    #[cfg(feature = "jit")]
    install_library_plugins();
    let root = e2e_root();
    let mut cases = Vec::new();
    collect_cases(&root, &mut cases);
    assert!(
        !cases.is_empty(),
        "no e2e `.cz` cases found under {}",
        root.display()
    );

    for pp in &cases {
        let src = fs::read_to_string(pp).expect("read case source");
        if let Some((lazy_passes, eager_passes)) = mode_expectations(&src) {
            // Expectation files per verdict: `.out` for a passing mode's
            // exact stdout, `.err` for a failing mode's diagnostics. A lazy
            // failure may legitimately report FEWER diagnostics than the
            // whole-program check (only the execution path's), so a
            // `.lazy.err` beside the case overrides `.err` for the lazy leg.
            let expect_out = || {
                fs::read_to_string(pp.with_extension("out"))
                    .unwrap_or_else(|_| panic!("{}: passing mode needs a .out", pp.display()))
            };
            let expect_err = || {
                fs::read_to_string(pp.with_extension("err"))
                    .unwrap_or_else(|_| panic!("{}: failing mode needs a .err", pp.display()))
            };
            let expect_lazy_err = || {
                fs::read_to_string(pp.with_extension("lazy.err")).unwrap_or_else(|_| expect_err())
            };
            // A JIT build runs both modes (default = lazy, --eager = eager);
            // an interpreter-only build checks eagerly regardless, so only
            // the @eager expectation applies there.
            #[cfg(feature = "jit")]
            {
                if lazy_passes {
                    check_success_mode(bin, pp, &expect_out(), false);
                } else {
                    check_error_mode(bin, pp, &expect_lazy_err(), false);
                }
                if eager_passes {
                    check_success_mode(bin, pp, &expect_out(), true);
                } else {
                    check_error_mode(bin, pp, &expect_err(), true);
                }
            }
            #[cfg(not(feature = "jit"))]
            {
                let _ = (lazy_passes, &expect_lazy_err);
                if eager_passes {
                    check_success(bin, pp, &expect_out());
                } else {
                    check_error(bin, pp, &expect_err());
                }
            }
            continue;
        }
        match (
            fs::read_to_string(pp.with_extension("out")).ok(),
            fs::read_to_string(pp.with_extension("err")).ok(),
        ) {
            (Some(expected), None) => check_success(bin, pp, &expected),
            (None, Some(expected)) => check_error(bin, pp, &expected),
            (Some(_), Some(_)) => {
                panic!(
                    "{} has both a .out and a .err expectation but no mode annotations",
                    pp.display()
                )
            }
            (None, None) => panic!("missing .out/.err expectation for {}", pp.display()),
        }
    }
}

/// `--eager` runs the whole check before execution instead of the default
/// lazy pipeline; both must produce identical output and status on a
/// demand-heavy case (reversed definition order, generic reuse).
#[test]
fn eager_flag_matches_the_lazy_pipeline() {
    let bin = env!("CARGO_BIN_EXE_brass");
    let pp = e2e_root().join("lazy/demand_chain.cz");
    let lazy = run_case(bin, &pp);
    let eager = Command::new(bin)
        .env("BRASS_CACHE", "off")
        .arg("--eager")
        .arg(&pp)
        .env("BRASS_PACKAGES", std_package_env())
        .output()
        .expect("spawn brass --eager");
    assert!(
        eager.status.success(),
        "--eager failed: {}",
        String::from_utf8_lossy(&eager.stderr)
    );
    assert_eq!(lazy.status.code(), eager.status.code());
    assert_eq!(
        String::from_utf8_lossy(&lazy.stdout),
        String::from_utf8_lossy(&eager.stdout),
    );
}

/// The interpreter's call-depth guard must fire before the host stack
/// overflows: runaway recursion through `brass repl` ends in the guard's
/// clean error, not a process abort. (The JIT intentionally uses the native
/// stack, so only the interpreter path is pinned here.)
#[test]
fn repl_deep_recursion_hits_the_depth_guard() {
    let bin = env!("CARGO_BIN_EXE_brass");
    let pp = Path::new(env!("CARGO_TARGET_TMPDIR")).join("repl_deep_recursion.cz");
    fs::write(
        &pp,
        "fun f(n: int64) -> int64 {\n    if n == 0 { return 0 }\n    return f(n - 1)\n}\nprintln(f(20000))\n",
    )
    .expect("write recursion case");
    let out = Command::new(bin)
        .env("BRASS_CACHE", "off")
        .arg("repl")
        .arg(&pp)
        .output()
        .expect("spawn brass");
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
