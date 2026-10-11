//! Native object reuse through both driver ORC execution paths.
#![cfg(feature = "jit")]

mod support;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Output;
use std::time::{SystemTime, UNIX_EPOCH};

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("jit-cache-{}-{nonce}", std::process::id()));
        fs::create_dir_all(&root).unwrap();
        Self(root)
    }

    fn source(&self, value: i32) -> PathBuf {
        let path = self.0.join("main.cz");
        fs::write(&path, format!(
            "fun answer() {{ return {value} }}\nfun other() {{ return 7 }}\nfun main() {{ println(answer() + other()) }}\n"
        )).unwrap();
        path
    }

    fn run(&self, source: &Path, enabled: bool) -> Output {
        let output = support::brass_command(env!("CARGO_BIN_EXE_brass"))
            .arg("--eager")
            .arg(source)
            .env("XDG_CACHE_HOME", self.0.join("cache"))
            .env("BRASS_JIT_CACHE", if enabled { "on" } else { "off" })
            .env("BRASS_JIT_CACHE_MAX_MB", "256")
            .env("BRASS_OPT", "0")
            .env(
                "BRASS_PACKAGES",
                format!(
                    "std={}",
                    Path::new(env!("CARGO_MANIFEST_DIR"))
                        .join("../..")
                        .display()
                ),
            )
            .env("BRASS_LOG", "brass::perf=debug")
            .env_remove("BRASS_LOG_TYPE")
            .output()
            .expect("run eager driver");
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        output
    }

    fn run_lazy(&self, source: &Path, tier: &str) -> Output {
        self.run_lazy_logged(source, tier, "brass::perf=debug")
    }

    fn run_lazy_logged(&self, source: &Path, tier: &str, log: &str) -> Output {
        self.run_logged(source, tier, log, false)
    }

    fn run_logged(&self, source: &Path, tier: &str, log: &str, eager: bool) -> Output {
        let output = support::brass_command(env!("CARGO_BIN_EXE_brass"))
            .args(eager.then_some("--eager"))
            .arg(source)
            .env("XDG_CACHE_HOME", self.0.join("cache"))
            .env("BRASS_JIT_CACHE", "on")
            .env("BRASS_JIT_CACHE_MAX_MB", "256")
            .env("BRASS_OPT", tier)
            .env(
                "BRASS_PACKAGES",
                format!(
                    "std={}",
                    Path::new(env!("CARGO_MANIFEST_DIR"))
                        .join("../..")
                        .display()
                ),
            )
            .env("BRASS_LOG", log)
            .env_remove("BRASS_LOG_TYPE")
            .output()
            .expect("run lazy driver");
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        output
    }

    fn objects(&self) -> Vec<PathBuf> {
        fs::read_dir(self.0.join("cache/brass/jit"))
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .collect()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// A second process skips native compilation, while editing a function changes
/// its content key and result. Disabling reads must also bypass existing hits.
#[test]
fn eager_cache_reuses_exact_ir_and_misses_after_edit() {
    let fixture = Fixture::new();
    let source = fixture.source(10);
    let first = fixture.run(&source, true);
    assert_eq!(first.stdout, b"17\n");
    let first_log = String::from_utf8_lossy(&first.stderr);
    assert!(first_log.contains("jit cache store"), "{first_log}");
    assert!(!first_log.contains("jit cache hit"), "{first_log}");
    let original_objects = fixture.objects();
    assert!(!original_objects.is_empty());

    let second = fixture.run(&source, true);
    assert_eq!(first.stdout, second.stdout);
    let second_log = String::from_utf8_lossy(&second.stderr);
    assert!(second_log.contains("jit cache hit"), "{second_log}");
    assert!(!second_log.contains("jit cache store"), "{second_log}");
    assert_eq!(fixture.objects().len(), original_objects.len());

    fixture.source(20);
    let edited = fixture.run(&source, true);
    assert_eq!(edited.stdout, b"27\n");
    let edited_log = String::from_utf8_lossy(&edited.stderr);
    assert!(edited_log.contains("jit cache store"), "{edited_log}");
    assert!(
        fixture
            .objects()
            .iter()
            .any(|path| !original_objects.contains(path))
    );
    let edited_again = fixture.run(&source, true);
    assert_eq!(edited_again.stdout, edited.stdout);
    assert!(!String::from_utf8_lossy(&edited_again.stderr).contains("jit cache store"));

    let disabled = fixture.run(&source, false);
    assert_eq!(disabled.stdout, edited.stdout);
    let disabled_log = String::from_utf8_lossy(&disabled.stderr);
    assert!(!disabled_log.contains("jit cache hit"));
    assert!(!disabled_log.contains("jit cache store"));
}

/// Opting out from a fresh process must not even create the cache directory.
#[test]
fn eager_cache_off_writes_nothing() {
    let fixture = Fixture::new();
    let source = fixture.source(10);
    let output = fixture.run(&source, false);
    assert_eq!(output.stdout, b"17\n");
    assert!(!fixture.0.join("cache").exists());
}

/// Objects must survive a native exit from JIT code, which bypasses session
/// destruction and any driver end-of-run hooks.
#[test]
fn eager_cache_publishes_before_native_exit() {
    let std_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std");
    for (package, library) in [
        ("brass_lib_process", "process"),
        ("brass_lib_fs", "fs"),
        ("brass_lib_path", "path"),
    ] {
        brass_plugin_host::fixture::install_plugin(package, library, &std_root);
    }
    let fixture = Fixture::new();
    let source = fixture.0.join("exit.cz");
    fs::write(&source, "import std.process.exit\nprintln(42)\nexit(0)\n").unwrap();
    let first = fixture.run(&source, true);
    assert_eq!(first.stdout, b"42\n");
    assert!(String::from_utf8_lossy(&first.stderr).contains("jit cache store"));
    assert!(!fixture.objects().is_empty());
    let second = fixture.run(&source, true);
    assert_eq!(first.stdout, second.stdout);
    let log = String::from_utf8_lossy(&second.stderr);
    assert!(log.contains("jit cache hit"), "{log}");
    assert!(!log.contains("jit cache store"), "{log}");
}

/// The default path stores both its startup entry group and the unannotated
/// function first specialized during execution, then reuses both in a new process.
#[test]
fn lazy_cache_reuses_startup_and_runtime_groups() {
    let fixture = Fixture::new();
    let source = fixture.source(10);
    let first = fixture.run_lazy(&source, "0");
    assert_eq!(first.stdout, b"17\n");
    let log = String::from_utf8_lossy(&first.stderr);
    assert!(
        log.lines()
            .any(|l| l.contains("lazy: runtime compile") && l.contains("answer")),
        "{log}"
    );
    for symbol in ["pp_fn_main", "pp_fn_answer"] {
        assert!(
            log.lines()
                .any(|l| l.contains("jit cache store") && l.contains(symbol)),
            "{log}"
        );
    }
    let second = fixture.run_lazy(&source, "0");
    assert_eq!(first.stdout, second.stdout);
    let log = String::from_utf8_lossy(&second.stderr);
    for symbol in ["pp_fn_main", "pp_fn_answer"] {
        assert!(
            log.lines()
                .any(|l| l.contains("jit cache hit") && l.contains(symbol)),
            "{log}"
        );
    }
    assert!(!log.contains("jit cache store"), "{log}");
}

/// Native exit bypasses Rust destructors: even runtime-resolved objects must be
/// published before control enters the exit primitive.
#[test]
fn lazy_cache_publishes_before_native_exit() {
    let std_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std");
    for (package, library) in [
        ("brass_lib_process", "process"),
        ("brass_lib_fs", "fs"),
        ("brass_lib_path", "path"),
    ] {
        brass_plugin_host::fixture::install_plugin(package, library, &std_root);
    }
    let fixture = Fixture::new();
    let source = fixture.0.join("exit.cz");
    fs::write(
        &source,
        "import std.process.exit\nfun answer() { return 42 }\nprintln(answer())\nexit(0)\n",
    )
    .unwrap();
    let first = fixture.run_lazy(&source, "0");
    assert_eq!(first.stdout, b"42\n");
    assert!(String::from_utf8_lossy(&first.stderr).contains("jit cache store"));
    assert!(!fixture.objects().is_empty());
    let second = fixture.run_lazy(&source, "0");
    assert_eq!(first.stdout, second.stdout);
    let log = String::from_utf8_lossy(&second.stderr);
    assert!(log.contains("jit cache hit"), "{log}");
    assert!(!log.contains("jit cache store"), "{log}");
}

/// BRASS_OPT selects the lazy session's IR and instruction-selection tier for
/// startup and runtime groups; an O2 run cannot consume the earlier O0 objects.
#[test]
fn lazy_opt_selects_o2_for_startup_and_runtime() {
    let fixture = Fixture::new();
    let source = fixture.source(10);
    let cold = fixture.run_lazy(&source, "0");
    let cold_log = String::from_utf8_lossy(&cold.stderr);
    assert!(
        cold_log
            .lines()
            .any(|l| l.contains("JIT session tier") && l.contains("O0")),
        "{cold_log}"
    );
    let optimized = fixture.run_lazy(&source, "2");
    assert_eq!(cold.stdout, optimized.stdout);
    let log = String::from_utf8_lossy(&optimized.stderr);
    assert!(
        log.lines()
            .any(|l| l.contains("JIT session tier") && l.contains("O2")),
        "{log}"
    );
    assert!(!log.contains("jit cache hit"), "{log}");
    for symbol in ["pp_fn_main", "pp_fn_answer"] {
        assert!(
            log.lines()
                .any(|l| l.contains("jit cache store") && l.contains(symbol)),
            "{log}"
        );
    }
    let warm = fixture.run_lazy(&source, "2");
    assert_eq!(warm.stdout, optimized.stdout);
    assert!(!String::from_utf8_lossy(&warm.stderr).contains("jit cache store"));
}

/// A runtime batch introduces spawn and its statically reached worker body.
/// Repeated fresh sessions exercise both cold materialization and cached objects;
/// the worker must only enter code materialized and primed on the main thread.
#[test]
fn lazy_runtime_spawn_materializes_new_worker_bodies() {
    let fixture = Fixture::new();
    let source = fixture.0.join("spawn.cz");
    fs::write(&source, "fun worker() -> int64 { return 42 }\nfun launch() {\n spawn(() -> { println(worker()) })\n sync()\n return 7\n}\nfun main() { println(launch()) }\n").unwrap();
    for _ in 0..12 {
        let output = fixture.run_lazy(&source, "0");
        assert_eq!(output.stdout, b"42\n7\n");
        let log = String::from_utf8_lossy(&output.stderr);
        for symbol in ["launch", "worker"] {
            assert!(
                log.lines()
                    .any(|l| l.contains("lazy: runtime compile") && l.contains(symbol)),
                "{log}"
            );
        }
    }
}

const SHARED_HELPERS: &str = r#"
type Box = { value: string, n: int64 }
fun first() -> int64 {
    let b = Box { value: "first", n: 11 }
    return b.n
}
fun second() -> int64 {
    let b = Box { value: "second", n: 22 }
    return b.n
}
fun main() {
    println(first())
    println(second())
}
"#;

/// Both groups import the same destructor, whose body occurs once in the IR.
/// A fresh process must execute both groups correctly from the cached objects.
#[test]
fn lazy_groups_share_one_destructor_across_cache_round_trip() {
    for eager in [true, false] {
        let fixture = Fixture::new();
        let source = fixture.0.join("helpers.cz");
        fs::write(&source, SHARED_HELPERS).unwrap();
        for warm in [false, true] {
            let output =
                fixture.run_logged(&source, "0", "brass::perf=debug,brass::ir=trace", eager);
            assert_eq!(output.stdout, b"11\n22\n");
            let log = String::from_utf8_lossy(&output.stderr);
            let destructors: Vec<_> = log
                .lines()
                .filter(|line| line.starts_with("define ") && line.contains("@pp_fn_drop_5f_Box"))
                .collect();
            assert_eq!(destructors.len(), 1, "{log}");
            assert!(!destructors[0].contains("private"), "{log}");
            let name = destructors[0]
                .split_once('@')
                .unwrap()
                .1
                .split('(')
                .next()
                .unwrap();
            assert_eq!(
                log.matches(&format!("declare void @{name}(")).count(),
                2,
                "{log}"
            );
            for group in ["first", "second"] {
                assert!(
                    log.contains(&format!("define i64 @__pp_lazy_body_pp_fn_{group}(")),
                    "{log}"
                );
            }
            if warm {
                assert!(log.contains("jit cache hit"), "{log}");
                assert!(!log.contains("jit cache store"), "{log}");
            }
        }
    }
}

/// Startup exports array glue; a runtime batch adds recursive record glue that
/// references it. Both batches must link in cold and fresh cached sessions.
#[test]
fn lazy_runtime_helper_module_links_to_startup_helpers() {
    let fixture = Fixture::new();
    let source = fixture.0.join("runtime-helpers.cz");
    fs::write(
        &source,
        r#"
type Node = { next: Node?, values: string[] }
fun later() {
    let node = Node { next: null, values: ["later"] }
    node.next = node
    return 42
}
fun main() {
    let seed = ["startup"]
    println(seed[0])
    println(later())
}
"#,
    )
    .unwrap();
    for _ in 0..2 {
        let output = fixture.run_lazy_logged(&source, "0", "brass::perf=debug,brass::ir=trace");
        assert_eq!(output.stdout, b"startup\n42\n");
        let log = String::from_utf8_lossy(&output.stderr);
        let (startup, runtime) = log
            .split_once("lazy: runtime compile symbol=later")
            .expect("runtime batch");
        assert!(startup.contains("; ModuleID = 'brass.helpers."), "{log}");
        assert!(
            runtime.contains("; ModuleID = 'brass.helpers.later'"),
            "{log}"
        );
        let startup_drop = startup
            .lines()
            .find(|line| line.starts_with("define ") && line.contains("@pp_fn_drop_"))
            .expect("startup destructor")
            .split_once('@')
            .unwrap()
            .1
            .split('(')
            .next()
            .unwrap();
        assert!(
            runtime.contains(&format!("declare void @{startup_drop}(")),
            "{log}"
        );
        assert!(
            !runtime
                .lines()
                .any(|line| line.starts_with("define ") && line.contains(startup_drop)),
            "{log}"
        );
    }
}

/// Isolated XDG storage must hit every previously stored group AND helper key
/// on an identical run. Debug logging alone exercises the production cache path.
#[test]
fn lazy_cache_hits_every_helper_module_key_in_a_fresh_process() {
    let fixture = Fixture::new();
    let source = fixture.0.join("helper-cache.cz");
    fs::write(&source, SHARED_HELPERS).unwrap();
    let first = fixture.run_lazy(&source, "0");
    let cold = String::from_utf8_lossy(&first.stderr);
    let stores: Vec<_> = cold
        .lines()
        .filter(|line| line.contains("jit cache store"))
        .collect();
    assert!(
        stores
            .iter()
            .any(|line| line.contains("symbol=\"pp_fn_trace_")),
        "{cold}"
    );
    let second = fixture.run_lazy(&source, "0");
    assert_eq!(second.stdout, first.stdout);
    let warm = String::from_utf8_lossy(&second.stderr);
    assert!(!warm.contains("jit cache store"), "{warm}");
    let hits: Vec<_> = warm
        .lines()
        .filter(|line| line.contains("jit cache hit"))
        .collect();
    assert_eq!(hits.len(), stores.len(), "{cold}\n{warm}");
    for store in stores {
        let key = store
            .split_whitespace()
            .find(|field| field.starts_with("key="))
            .expect("cache key");
        assert!(
            hits.iter().any(|line| line.contains(key)),
            "missing {key}: {warm}"
        );
    }
}
