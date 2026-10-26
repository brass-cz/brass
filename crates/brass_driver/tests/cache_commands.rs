//! Cache management commands operate on isolated storage without compiling input.

mod support;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("cache-commands-{}-{nonce}", std::process::id()));
        fs::create_dir_all(&root).unwrap();
        Self(root)
    }

    fn command(&self) -> Command {
        let mut command = support::brass_command(env!("CARGO_BIN_EXE_brass"));
        command
            .current_dir(&self.0)
            .env("XDG_CACHE_HOME", self.0.join("xdg"))
            .env("HOME", self.0.join("home"))
            .env("BRASS_JIT_CACHE", "on")
            .env("BRASS_JIT_CACHE_MAX_MB", "2")
            .env_remove("BRASS_LOG")
            .env_remove("BRASS_LOG_TYPE");
        command
    }

    fn cache(&self) -> PathBuf {
        self.0.join("xdg/brass/jit")
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn success(output: Output) -> String {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

/// Info and clean work on missing and disabled stores, preserving unknown files.
#[test]
fn cache_info_and_clean() {
    let fixture = Fixture::new();
    let empty = success(fixture.command().args(["cache", "info"]).output().unwrap());
    if !cfg!(feature = "jit") {
        assert_eq!(empty, "This build has no JIT cache.\n");
        assert_eq!(
            success(fixture.command().args(["cache", "clean"]).output().unwrap()),
            empty
        );
        assert!(!fixture.cache().exists());
        return;
    }
    assert!(
        empty.contains(&format!("Directory: {}\n", fixture.cache().display())),
        "{empty}"
    );
    assert!(empty.contains("Status: enabled"), "{empty}");
    assert!(empty.contains("Entries: 0\n"), "{empty}");
    assert!(empty.contains("Size: 0.00 B (0 bytes)\n"), "{empty}");
    assert!(
        empty.contains("Limit: 2.00 MiB (2097152 bytes)\n"),
        "{empty}"
    );
    assert!(empty.contains("Stale temp files: 0\n"), "{empty}");
    success(fixture.command().args(["cache", "clean"]).output().unwrap());
    assert!(!fixture.cache().exists());

    fs::create_dir_all(fixture.cache()).unwrap();
    let object = fixture.cache().join(format!("{}.czobj", "a".repeat(64)));
    fs::write(&object, b"object").unwrap();
    fs::write(fixture.cache().join("foreign.czobj"), b"foreign").unwrap();
    let info = success(
        fixture
            .command()
            .args(["cache", "info"])
            .env("BRASS_JIT_CACHE", "off")
            .output()
            .unwrap(),
    );
    assert!(
        info.contains("Status: disabled (BRASS_JIT_CACHE=off or 0)"),
        "{info}"
    );
    assert!(info.contains("Entries: 1\n"), "{info}");
    assert!(info.contains("Size: 6.00 B (6 bytes)\n"), "{info}");
    let clean = success(
        fixture
            .command()
            .args(["cache", "clean"])
            .env("BRASS_JIT_CACHE", "0")
            .output()
            .unwrap(),
    );
    assert!(clean.contains("Removed entries: 1\n"), "{clean}");
    assert!(
        clean.contains("Removed size: 6.00 B (6 bytes)\n"),
        "{clean}"
    );
    assert!(!object.exists());
    assert!(fixture.cache().join("foreign.czobj").exists());
    let flagged = success(
        fixture
            .command()
            .args(["--no-jit-cache", "cache", "info"])
            .output()
            .unwrap(),
    );
    assert!(flagged.contains("disabled (--no-jit-cache)"), "{flagged}");
}

/// No-JIT builds acknowledge management commands; JIT builds report I/O errors
/// with status 1 and explain unavailable environment configuration.
#[test]
fn cache_configuration_and_errors() {
    let fixture = Fixture::new();
    let absent = success(
        fixture
            .command()
            .args(["cache", "info"])
            .env_remove("HOME")
            .env_remove("XDG_CACHE_HOME")
            .output()
            .unwrap(),
    );
    if !cfg!(feature = "jit") {
        assert_eq!(absent, "This build has no JIT cache.\n");
        return;
    }
    assert!(
        absent.contains("disabled (neither XDG_CACHE_HOME nor HOME is set)"),
        "{absent}"
    );
    let fallback = success(
        fixture
            .command()
            .args(["cache", "info"])
            .env_remove("XDG_CACHE_HOME")
            .output()
            .unwrap(),
    );
    assert!(
        fallback.contains(&format!(
            "Directory: {}",
            fixture.0.join("home/.cache/brass/jit").display()
        )),
        "{fallback}"
    );
    fs::create_dir_all(fixture.cache().parent().unwrap()).unwrap();
    fs::write(fixture.cache(), b"not a directory").unwrap();
    for action in ["info", "clean"] {
        let output = fixture.command().args(["cache", action]).output().unwrap();
        assert_eq!(output.status.code(), Some(1));
        assert!(String::from_utf8_lossy(&output.stderr).contains("JIT cache:"));
    }
}

/// The flag disables reads and writes in lazy and eager runs even when the
/// environment enables caching. It does not delete objects already present.
#[test]
fn no_jit_cache_bypasses_reads_and_writes() {
    let fixture = Fixture::new();
    let source = fixture.0.join("main.cz");
    fs::write(&source, "fun main() { println(42) }\n").unwrap();
    for eager in [false, true] {
        let run = || {
            let output = fixture
                .command()
                .args(eager.then_some("--eager"))
                .arg("--no-jit-cache")
                .arg(&source)
                .env("BRASS_LOG", "brass::perf=debug")
                .output()
                .unwrap();
            let log = String::from_utf8_lossy(&output.stderr);
            assert!(!log.contains("jit cache hit"), "{log}");
            assert!(!log.contains("jit cache store"), "{log}");
            assert_eq!(success(output), "42\n");
        };
        run();
        assert!(!fixture.cache().exists());
        success(
            fixture
                .command()
                .args(eager.then_some("--eager"))
                .arg(&source)
                .output()
                .unwrap(),
        );
        if cfg!(feature = "jit") {
            let before: Vec<_> = fs::read_dir(fixture.cache())
                .unwrap()
                .map(|entry| {
                    let path = entry.unwrap().path();
                    let metadata = fs::metadata(&path).unwrap();
                    (path, metadata.len(), metadata.modified().unwrap())
                })
                .collect();
            assert!(!before.is_empty());
            run();
            assert_eq!(fs::read_dir(fixture.cache()).unwrap().count(), before.len());
            for (path, len, modified) in before {
                let metadata = fs::metadata(path).unwrap();
                assert_eq!(
                    (metadata.len(), metadata.modified().unwrap()),
                    (len, modified)
                );
            }
            success(fixture.command().args(["cache", "clean"]).output().unwrap());
            fs::remove_dir(fixture.cache()).unwrap();
        }
    }
}

/// A reserved command word becomes a program filename after the separator.
#[test]
fn cache_filename_requires_separator() {
    let fixture = Fixture::new();
    fs::write(fixture.0.join("cache"), "println(42)\n").unwrap();
    assert!(
        !fixture
            .command()
            .arg("cache")
            .output()
            .unwrap()
            .status
            .success()
    );
    assert_eq!(
        success(
            fixture
                .command()
                .args(["--no-jit-cache", "--", "cache"])
                .output()
                .unwrap()
        ),
        "42\n"
    );
}
