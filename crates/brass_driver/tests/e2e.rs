//! End-to-end tests of the language. Each `*.cz` under `e2e_tests/` is run
//! through the driver and checked against a sibling expectation. Two
//! expectation kinds are supported:
//!
//! - `*.out`: the program must run successfully and its stdout must match the file
//!   byte-for-byte (the common success case).
//! - `*.err`: the program must *fail* (non-zero exit) and its stderr must contain
//!   each of the file's trimmed lines as a substring. This pins the diagnostics
//!   for programs that must be rejected.
//!
//! Leading annotation lines choose the runs: `// @backends: all` runs the case
//! on the lazy JIT, `--eager` and the REPL interpreter against one expectation;
//! `// @lazy:` and `// @eager:` give per-mode verdicts (see [`case_modes`]).
//!
//! Cases are grouped by subsystem (`field/`, `variant/`, `types/`, `structure/`,
//! `references/`, ...). `concurrency/` cases use `spawn`/`with`, which only the JIT
//! back end runs, so that directory is skipped when the `jit` feature is off (the
//! interpreter rejects concurrency at runtime).

mod support;

use std::fs;
use std::path::{Path, PathBuf};

fn e2e_root() -> PathBuf {
    // The driver manifest lives at crates/brass_driver; the repo root is two up.
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../e2e_tests")
}

/// Every `*.cz` under `dir`, recursively, in sorted order (so failures are stable).
/// `concurrency/` is skipped without the `jit` feature (real threads need the
/// JIT back end), and so are the standard-library directories (`net/`,
/// `process/`, `fs/`, `regex/`, ...) -- not because the interpreter cannot run
/// them, but because only the JIT configuration builds the native plugins the
/// libraries import.
fn collect_cases(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .map(|e| e.unwrap().path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            if path.file_name().is_some_and(|name| name == "net")
                && std::env::var_os("BRASS_E2E_SKIP_NET").is_some()
            {
                // Restricted test sandboxes may deny even loopback sockets;
                // keep the remainder of the default-feature suite runnable.
                continue;
            }
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
#[cfg(feature = "jit")]
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

/// One way of running a case. `Lazy` is the default pipeline, `Eager` inserts
/// `--eager` (the whole-program check before execution) and `Repl` runs the
/// file through `brass repl`, the interpreter back end. An interpreter-only
/// build checks eagerly either way, so there every leg runs the interpreter.
#[derive(Clone, Copy, Debug)]
enum Leg {
    Lazy,
    Eager,
    Repl,
}

/// [`run_case`] on a chosen [`Leg`].
fn run_case_leg(bin: &str, pp: &Path, leg: Leg) -> std::process::Output {
    let mut cmd = support::brass_command(bin);
    match leg {
        Leg::Lazy => {}
        Leg::Eager => {
            cmd.arg("--eager");
        }
        Leg::Repl => {
            cmd.arg("repl");
        }
    }
    cmd.arg(pp)
        .env("BRASS_PACKAGES", std_package_env())
        .output()
        .expect("spawn brass")
}

/// [`run_case`] with the check mode chosen: `eager` inserts `--eager` before
/// the file, forcing the whole-program check the annotated cases pin per
/// mode.
fn run_case_mode(bin: &str, pp: &Path, eager: bool) -> std::process::Output {
    run_case_leg(bin, pp, if eager { Leg::Eager } else { Leg::Lazy })
}

/// The expectation scheme a case's leading annotation lines select.
#[derive(Debug, PartialEq, Eq)]
enum CaseModes {
    /// No annotation: one run in the default mode against the single
    /// `.out` or `.err` beside the case.
    Default,
    /// `// @lazy:` and `// @eager:` lines: per-mode verdicts (pass/fail).
    PerMode {
        lazy_passes: bool,
        eager_passes: bool,
    },
    /// `// @backends: all`: the lazy JIT, `--eager` and the REPL interpreter
    /// must all meet the single `.out` or `.err`. Cases that pin a value both
    /// back ends must agree on use this, so a divergence fails the suite.
    AllBackends,
}

/// Expectations parsed from a case's leading annotation lines:
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
/// substring) and runs in both modes.
///
/// ```text
/// // @backends: all
/// ```
///
/// runs the case on every leg (see [`CaseModes::AllBackends`]) against its
/// single expectation; it cannot be combined with `@lazy`/`@eager`.
/// Unannotated cases keep the single-expectation behavior. The grammar is
/// strict -- a typo must fail the suite, not silently skip an expectation.
fn case_modes(src: &str) -> CaseModes {
    let mut lazy = None;
    let mut eager = None;
    let mut all_backends = false;
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
        if mode.trim() == "backends" {
            match value.trim() {
                "all" => all_backends = true,
                other => panic!("`@backends` value must be `all`, got `{other}`"),
            }
            continue;
        }
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
    match (lazy, eager, all_backends) {
        (None, None, false) => CaseModes::Default,
        (None, None, true) => CaseModes::AllBackends,
        (Some(lazy_passes), Some(eager_passes), false) => CaseModes::PerMode {
            lazy_passes,
            eager_passes,
        },
        (_, _, true) => panic!("`@backends: all` cannot be combined with @lazy/@eager"),
        _ => panic!("a case with mode annotations must specify both @lazy and @eager"),
    }
}

/// Run a success case: the program must exit zero and print exactly `expected`.
fn check_success(bin: &str, pp: &Path, expected: &str) {
    check_success_leg(bin, pp, expected, Leg::Lazy)
}

fn check_success_mode(bin: &str, pp: &Path, expected: &str, eager: bool) {
    check_success_leg(
        bin,
        pp,
        expected,
        if eager { Leg::Eager } else { Leg::Lazy },
    )
}

fn check_success_leg(bin: &str, pp: &Path, expected: &str, leg: Leg) {
    let out = run_case_leg(bin, pp, leg);
    assert!(
        out.status.success(),
        "{} failed to run on {leg:?} (status {:?})\nstderr:\n{}",
        pp.display(),
        out.status.code(),
        String::from_utf8_lossy(&out.stderr),
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !stderr.contains(": warning:"),
        "{} produced an unpinned checker warning on {leg:?}:\n{stderr}",
        pp.display(),
    );
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        expected,
        "{} produced unexpected stdout on {leg:?}",
        pp.display(),
    );
}

/// Run an error case: the program must exit non-zero and its stderr must contain
/// every line of `expected` (trimmed) as a substring, so the diagnostic is pinned
/// without coupling to the absolute source path the driver prints.
fn check_error(bin: &str, pp: &Path, expected: &str) {
    check_error_leg(bin, pp, expected, Leg::Lazy)
}

fn check_error_mode(bin: &str, pp: &Path, expected: &str, eager: bool) {
    check_error_leg(
        bin,
        pp,
        expected,
        if eager { Leg::Eager } else { Leg::Lazy },
    )
}

fn check_error_leg(bin: &str, pp: &Path, expected: &str, leg: Leg) {
    let out = run_case_leg(bin, pp, leg);
    assert!(
        !out.status.success(),
        "{} was expected to fail on {leg:?} but succeeded\nstdout:\n{}",
        pp.display(),
        String::from_utf8_lossy(&out.stdout),
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    for needle in expected.lines().map(str::trim).filter(|l| !l.is_empty()) {
        assert!(
            stderr.contains(needle),
            "{} stderr on {leg:?} did not contain `{needle}`\nstderr:\n{stderr}",
            pp.display(),
        );
    }
}

#[test]
fn completion_chain_errors_preserve_output_boundaries() {
    // Error expectations normally pin only diagnostics. These chains also pin
    // the exit status and whether execution reached the print before the call.
    let bin = env!("CARGO_BIN_EXE_brass");
    for name in [
        "completion_chain_type_error",
        "completion_chain_runtime_error",
    ] {
        let path = e2e_root().join("lazy").join(format!("{name}.cz"));
        let expected_out = fs::read(path.with_extension("out")).expect("read stdout expectation");
        let expected_err =
            fs::read_to_string(path.with_extension("err")).expect("read diagnostic expectation");
        let mut previous = None;
        for leg in [Leg::Lazy, Leg::Eager] {
            let output = run_case_leg(bin, &path, leg);
            assert_eq!(output.status.code(), Some(1), "{name} on {leg:?}");
            assert_eq!(output.stdout, expected_out, "{name} on {leg:?}");
            assert!(
                String::from_utf8_lossy(&output.stderr).contains(expected_err.trim()),
                "{name} on {leg:?}: {}",
                String::from_utf8_lossy(&output.stderr),
            );
            if let Some(stderr) = previous {
                assert_eq!(
                    output.stderr, stderr,
                    "{name}: lazy/eager diagnostic parity"
                );
            }
            previous = Some(output.stderr);
        }
        #[cfg(feature = "jit")]
        {
            // Keep both fixtures inside completion eligibility so these tests
            // exercise early dedicated passes, not an ineligible fallback.
            let traced = support::brass_command(bin)
                .env("BRASS_LOG", "brass::perf=debug")
                .arg(&path)
                .output()
                .expect("trace completion fixture");
            assert_eq!(traced.status.code(), Some(1), "{name}");
            assert_eq!(traced.stdout, expected_out, "{name}");
            assert!(
                String::from_utf8_lossy(&traced.stderr)
                    .contains("check: completion eligibility symbol=f1 eligibility=Closed"),
                "{name}: {}",
                String::from_utf8_lossy(&traced.stderr),
            );
        }
    }
}

#[test]
fn parser_review_diagnostics_precede_execution_in_every_mode() {
    // Rejected bodies must fail before execution in every mode that checks them.
    // Uncalled bodies use explicit mode expectations and still fail `check`.
    let bin = env!("CARGO_BIN_EXE_brass");
    let mut cases = Vec::new();
    collect_cases(&e2e_root().join("parser_review"), &mut cases);
    for path in cases {
        let Ok(expected) = fs::read_to_string(path.with_extension("err")) else {
            continue;
        };
        let source = fs::read_to_string(&path).expect("read parser review case");
        let lazy_passes = matches!(
            case_modes(&source),
            CaseModes::PerMode {
                lazy_passes: true,
                ..
            }
        );
        for mode in [Some("check"), Some("--eager"), None] {
            if mode.is_none() && lazy_passes && cfg!(feature = "jit") {
                let stdout = fs::read_to_string(path.with_extension("out"))
                    .expect("lazy success case needs stdout");
                check_success(bin, &path, &stdout);
                continue;
            }
            let output = support::brass_command(bin)
                .args(mode)
                .arg(&path)
                .output()
                .expect("run parser review case");
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                !output.status.success(),
                "{} {mode:?}: {stderr}",
                path.display()
            );
            assert!(
                output.stdout.is_empty(),
                "{} {mode:?} executed before rejection",
                path.display()
            );
            for message in expected.lines().filter(|line| !line.is_empty()) {
                assert!(
                    stderr.contains(message),
                    "{} {mode:?}: missing {message:?}: {stderr}",
                    path.display()
                );
            }
        }
    }
}

#[test]
fn e2e_cases_produce_expected_output() {
    let bin = env!("CARGO_BIN_EXE_brass");
    // The standard-library cases import libraries whose native halves are
    // plugins; build them into `std/` as `std/build.sh` would. Only this
    // configuration builds the plugins, so only it runs those cases (see
    // `collect_cases`).
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
        let modes = case_modes(&src);
        if modes == CaseModes::AllBackends {
            let out = fs::read_to_string(pp.with_extension("out")).ok();
            let err = fs::read_to_string(pp.with_extension("err")).ok();
            // The interpreter-only build has no JIT legs: every leg would
            // run the interpreter, so one run covers it.
            let legs: &[Leg] = if cfg!(feature = "jit") {
                &[Leg::Lazy, Leg::Eager, Leg::Repl]
            } else {
                &[Leg::Lazy]
            };
            for &leg in legs {
                match (&out, &err) {
                    (Some(expected), None) => check_success_leg(bin, pp, expected, leg),
                    (None, Some(expected)) => check_error_leg(bin, pp, expected, leg),
                    _ => panic!(
                        "{}: `@backends: all` needs exactly one of .out/.err",
                        pp.display()
                    ),
                }
            }
            continue;
        }
        if let CaseModes::PerMode {
            lazy_passes,
            eager_passes,
        } = modes
        {
            // Expectation files per verdict: `.out` for a passing mode's
            // exact stdout, `.err` for a failing mode's diagnostics. A failed
            // lazy run reports the checker's complete verdict, like the
            // whole-program check, so both failing legs share the `.err`.
            let expect_out = || {
                fs::read_to_string(pp.with_extension("out"))
                    .unwrap_or_else(|_| panic!("{}: passing mode needs a .out", pp.display()))
            };
            let expect_err = || {
                fs::read_to_string(pp.with_extension("err"))
                    .unwrap_or_else(|_| panic!("{}: failing mode needs a .err", pp.display()))
            };
            // A JIT build runs both modes (default = lazy, --eager = eager);
            // an interpreter-only build checks eagerly regardless, so only
            // the @eager expectation applies there.
            #[cfg(feature = "jit")]
            {
                if lazy_passes {
                    check_success_mode(bin, pp, &expect_out(), false);
                } else {
                    check_error_mode(bin, pp, &expect_err(), false);
                }
                if eager_passes {
                    check_success_mode(bin, pp, &expect_out(), true);
                } else {
                    check_error_mode(bin, pp, &expect_err(), true);
                }
            }
            #[cfg(not(feature = "jit"))]
            {
                let _ = lazy_passes;
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
    let eager = support::brass_command(bin)
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

/// A checker warning never fails a run, and every mode renders it through the
/// same formatter. The runs also pin that analysis state is never persisted:
/// nothing appears beside the entry file, and only native objects may appear
/// under `XDG_CACHE_HOME`.
#[test]
fn checker_warning_is_nonfatal_in_every_mode() {
    let bin = env!("CARGO_BIN_EXE_brass");
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock after epoch")
        .as_nanos();
    let root = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("checker_warning-{}-{nonce}", std::process::id()));
    fs::create_dir_all(&root).expect("create warning directory");
    let cache_home = root.join("xdg-cache");
    let source = root.join("mixed.cz");
    fs::write(
        &source,
        concat!(
            "fun mixed(c: int32) {\n",
            "    if c == 1 {\n",
            "        error(\"a\")!\n",
            "    } else if c == 2 {\n",
            "        null!\n",
            "    }\n",
            "    return 7\n",
            "}\n",
            "\n",
            "fun main() {\n",
            "    let result = mixed(0)\n",
            "    if result {\n",
            "        match result {\n",
            "            Ok { value } => println(value),\n",
            "            Err { error } => println(error),\n",
            "        }\n",
            "    }\n",
            "}\n",
        ),
    )
    .expect("write warning program");
    let expected_warning = format!(
        "{}:1:1: warning: `mixed` returns `Result<int32, Error>?`: the body \
         propagates both null ({}:5:9) and errors ({}:3:9), so callers must unwrap two \
         layers; convert the null with `.context(message)` or annotate the return type\n",
        source.display(),
        source.display(),
        source.display(),
    );

    for (mode, args, expected_stdout) in [
        (
            "eager",
            vec![std::ffi::OsStr::new("--eager"), source.as_os_str()],
            "7\n",
        ),
        ("lazy", vec![source.as_os_str()], "7\n"),
        (
            "check",
            vec![std::ffi::OsStr::new("check"), source.as_os_str()],
            "",
        ),
        (
            "repl",
            vec![std::ffi::OsStr::new("repl"), source.as_os_str()],
            "7\n",
        ),
    ] {
        let output = support::brass_command(bin)
            .env("XDG_CACHE_HOME", &cache_home)
            .args(args)
            .output()
            .unwrap_or_else(|error| panic!("run {mode} warning program: {error}"));
        assert!(
            output.status.success(),
            "{mode} warning run failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&output.stdout), expected_stdout);
        assert_eq!(
            String::from_utf8_lossy(&output.stderr),
            expected_warning,
            "{mode} must use the common warning formatter"
        );
    }
    let entries: Vec<_> = fs::read_dir(&root)
        .expect("list warning directory")
        .map(|entry| entry.expect("directory entry").file_name())
        .filter(|name| name != "xdg-cache")
        .collect();
    assert_eq!(
        entries,
        ["mixed.cz"],
        "runs must not leave artifacts beside the entry"
    );
    fn check_cache_tree(root: &Path, dir: &Path) {
        if !dir.exists() {
            return;
        }
        for entry in fs::read_dir(dir).expect("list cache directory") {
            let path = entry.expect("cache entry").path();
            let relative = path.strip_prefix(root).unwrap();
            if path.is_dir() {
                assert!(relative == Path::new("brass") || relative == Path::new("brass/jit"));
                check_cache_tree(root, &path);
            } else {
                assert_eq!(relative.parent(), Some(Path::new("brass/jit")));
                assert_eq!(path.extension().and_then(|ext| ext.to_str()), Some("czobj"));
            }
        }
    }
    check_cache_tree(&cache_home, &cache_home);
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
    let out = support::brass_command(bin)
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

/// A record of one declaration stored in a slot annotated with another
/// declaration (a wider record with the same fields plus one) is rejected
/// before anything runs: a `let` slot is a storage site, which takes only
/// values of its own declaration, and the two declarations lay their fields
/// out differently.
#[cfg(feature = "jit")]
#[test]
fn record_of_another_declaration_never_reaches_a_typed_slot() {
    let pp = Path::new(env!("CARGO_TARGET_TMPDIR")).join("record_other_declaration.cz");
    fs::write(
        &pp,
        "type Point = {\n    x: int64\n    y: int64\n}\n\
         type P3 = {\n    z: float64\n    x: int64\n    y: int64\n}\n\
         fun main() {\n    let p = P3 { z: 1.5, x: 1, y: 2 }\n    \
         let q: Point = p\n    println(q.x + q.y)\n}\n",
    )
    .expect("write record flow case");
    let out = support::brass_command(env!("CARGO_BIN_EXE_brass"))
        .arg(&pp)
        .output()
        .expect("spawn brass");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(!out.status.success(), "expected failure; stderr:\n{stderr}");
    assert!(
        out.stdout.is_empty(),
        "{}",
        String::from_utf8_lossy(&out.stdout)
    );
    assert!(stderr.contains("`Point"), "{stderr}");
}

/// Ownership warnings describe actual access guards, once per scope and root.
#[cfg(feature = "jit")]
#[test]
fn auto_guard_warnings_follow_inserted_accesses() {
    let bin = env!("CARGO_BIN_EXE_brass");
    let cases: &[(&str, &[(&str, &str)])] = &[
        ("tasks_only", &[]),
        ("explicit_access", &[]),
        ("direct_access", &[("counter", "in `main`")]),
        ("alias_access", &[("counter", "in `main`")]),
        ("named_task", &[("counter", "in `main`")]),
        ("helper_task", &[("counter", "in `main`")]),
        (
            "nested_task",
            &[("counter", "in a spawned task within `main`")],
        ),
        ("deferred_closure", &[]),
        (
            "method_access",
            &[("self", "in `Counter.run`"), ("counter", "in `main`")],
        ),
        ("grouped_access", &[("a", "in `main`"), ("b", "in `main`")]),
    ];
    for (case, warnings) in cases {
        let path = e2e_root().join(format!("concurrency/auto_guard_{case}.cz"));
        let expected_stdout = fs::read_to_string(path.with_extension("out")).unwrap();
        for mode in [Some("check"), None, Some("--eager")] {
            let output = support::brass_command(bin)
                .args(mode)
                .arg(&path)
                .output()
                .unwrap();
            let stderr = String::from_utf8(output.stderr).unwrap();
            assert!(output.status.success(), "{case} {mode:?}: {stderr}");
            assert_eq!(
                String::from_utf8(output.stdout).unwrap(),
                if mode == Some("check") {
                    ""
                } else {
                    &expected_stdout
                }
            );
            let expected: String = warnings.iter().map(|(root, scope)| format!(
                "warning: variable '{root}' is shared with a spawned task; accesses outside `with` are auto-guarded by its cown lock {scope}\n  = note: for finer-grained concurrency, acquire it explicitly with 'with(cown, (c) -> {{ ... }})'\n"
            )).collect();
            assert_eq!(stderr, expected, "{case} {mode:?}");
        }
    }
}

/// Array reads and writes use identical complete diagnostic text on every backend.
#[test]
fn bounds_errors_match_exactly_across_backends() {
    let bin = env!("CARGO_BIN_EXE_brass");
    for operation in ["load", "store"] {
        for shape in ["fixed", "negative", "empty", "growable"] {
            let path = e2e_root().join(format!("array/index_out_of_bounds_{operation}_{shape}.cz"));
            for leg in [Leg::Lazy, Leg::Eager, Leg::Repl] {
                let output = run_case_leg(bin, &path, leg);
                assert!(!output.status.success(), "{} {leg:?}", path.display());
                assert!(output.stdout.is_empty());
                assert_eq!(
                    String::from_utf8(output.stderr).unwrap(),
                    "runtime error: array index out of bounds\n",
                    "{} {leg:?}",
                    path.display()
                );
            }
        }
    }
}

/// An eager entry point that cannot be instantiated explains the missing compilation.
#[cfg(feature = "jit")]
#[test]
fn eager_main_parameter_reports_compilation_failure() {
    let path = e2e_root().join("runtime/main_requires_arguments.cz");
    let output = run_case_leg(env!("CARGO_BIN_EXE_brass"), &path, Leg::Eager);
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert_eq!(
        String::from_utf8(output.stderr).unwrap(),
        "runtime error: cannot compile `main` for execution\n"
    );
}
