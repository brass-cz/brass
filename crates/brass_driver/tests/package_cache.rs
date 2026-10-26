//! Offline package-cache management against isolated, pre-populated stores.

#![cfg(all(feature = "jit", unix))]

mod support;

use std::fs::{self, File, FileTimes};
use std::os::unix::fs::{PermissionsExt, symlink};
use std::path::{Path, PathBuf};
use std::process::Output;
use std::time::{SystemTime, UNIX_EPOCH};

const PARENT: &str = "5d7229309d6e8dc3520481d1c965e80684329046e301071dc0a299103d2d0e8c";
const LEAF: &str = "6779ea0892aa9897bfea7a2826f44a320b3b15f62d0136ec81124f4f3c25f55f";

struct Fixture {
    root: PathBuf,
    home: PathBuf,
    project: PathBuf,
    store: PathBuf,
}

impl Fixture {
    fn new() -> Self {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        for library in ["process", "path", "fs", "hash", "env", "regex"] {
            brass_plugin_host::fixture::install_plugin(
                &format!("brass_lib_{library}"),
                library,
                &repo.join("std"),
            );
        }
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!("brass_cache-{}-{nonce}", std::process::id()));
        let home = root.join("home");
        let project = root.join("project");
        let store = home.join(".brass/packages");
        fs::create_dir_all(&home).unwrap();
        fs::create_dir_all(&project).unwrap();
        fs::create_dir_all(root.join("bin")).unwrap();
        fs::write(
            root.join("czpm.cz"),
            "import std.package_manager.exec.main\n\nmain()!\n",
        )
        .unwrap();
        // Any attempt to resolve or fetch remotely must fail and leave evidence.
        for tool in ["git", "curl", "wget", "tar"] {
            let path = root.join("bin").join(tool);
            fs::write(
                &path,
                "#!/bin/sh\nprintf '%s\\n' forbidden >> \"$HOME/network-attempt\"\nexit 91\n",
            )
            .unwrap();
            fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
        }
        Self {
            root,
            home,
            project,
            store,
        }
    }

    fn run(&self, args: &[&str], in_package: bool) -> Output {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let output = support::brass_command(env!("CARGO_BIN_EXE_brass"))
            .current_dir(if in_package {
                &self.project
            } else {
                &self.root
            })
            .env("HOME", &self.home)
            .env(
                "PATH",
                format!(
                    "{}:{}:{}",
                    self.root.join("bin").display(),
                    Path::new(env!("CARGO_BIN_EXE_brass"))
                        .parent()
                        .unwrap()
                        .display(),
                    std::env::var("PATH").unwrap_or_default()
                ),
            )
            .env("BRASS_PACKAGES", format!("std={}", repo.display()))
            .env("BRASS_JIT_CACHE", "off")
            .arg(self.root.join("czpm.cz"))
            .args(args)
            .output()
            .unwrap();
        assert!(
            !self.home.join("network-attempt").exists(),
            "cache command spawned a fetch tool"
        );
        output
    }

    fn success(&self, args: &[&str], in_package: bool) -> String {
        let output = self.run(args, in_package);
        assert!(
            output.status.success(),
            "{args:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).unwrap()
    }

    fn failure(&self, args: &[&str], in_package: bool, message: &str) {
        let output = self.run(args, in_package);
        assert!(!output.status.success(), "{args:?}: unexpectedly succeeded");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(message),
            "{args:?}: expected {message:?} in {stderr}"
        );
    }

    fn entry(&self, kind: &str, name: &str) -> PathBuf {
        let path = self.store.join(kind).join(name);
        fs::create_dir_all(&path).unwrap();
        path
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.root).unwrap();
    }
}

fn manifest(root: &Path, deps: &str) {
    fs::create_dir_all(root).unwrap();
    fs::write(root.join("package.toml"), format!("[package]\nname = \"fixture\"\nauthors = \"\"\nlicense = \"MIT\"\n[dependencies]\n{deps}\n")).unwrap();
}

fn age(path: &Path) {
    File::open(path)
        .unwrap()
        .set_times(FileTimes::new().set_modified(UNIX_EPOCH))
        .unwrap();
}

#[test]
fn offline_graph_selection_and_owned_tree_cleanup() {
    let f = Fixture::new();
    let a = "a".repeat(64);
    let b = "b".repeat(64);
    let c = "c".repeat(64);
    let parent = f.entry("git", PARENT);
    let leaf = f.entry("git", LEAF);
    let archive = f.entry("tarball", &a);
    let child = f.entry("tarball", &b);
    let orphan = f.entry("tarball", &c);
    let local = f.project.join("local");
    manifest(
        &f.project,
        &format!(
            "parent = {{ git = \"https://example.invalid/parent.git\", rev = \"abc123\" }}\narchive = {{ tarball = \"https://example.invalid/a.tar.gz\", hash = \"{a}\" }}\nlocal = {{ path = \"local\" }}\nmissing = {{ git = \"https://example.invalid/missing.git\", rev = \"v1\" }}"
        ),
    );
    manifest(
        &parent,
        &format!("child = {{ tarball = \"https://example.invalid/b.tar.gz\", hash = \"{b}\" }}"),
    );
    // The cached child loops back to its parent; the local path supplies another branch.
    manifest(
        &child,
        "parent = { git = \"https://example.invalid/parent.git\", rev = \"abc123\" }",
    );
    manifest(
        &local,
        "leaf = { git = \"https://example.invalid/leaf.git\", rev = \"v1\" }",
    );
    fs::write(orphan.join("payload"), vec![0; 2048]).unwrap();
    let stale = f.entry("git", &format!(".{PARENT}.123"));
    fs::write(stale.join("payload"), "old").unwrap();
    age(&stale.join("payload"));
    age(&stale);
    let fresh = f.entry("tarball", &format!(".{a}.456"));
    let active = f.entry("tarball", &format!(".{b}.789"));
    fs::write(active.join("payload"), "fresh").unwrap();
    age(&active);
    let foreign = f.entry("git", "notes");
    let malformed = f.entry("git", &format!(".{PARENT}.0123"));
    age(&malformed);
    fs::write(f.store.join("git").join("d".repeat(64)), "ordinary file").unwrap();
    let outside = f.root.join("outside");
    fs::create_dir_all(&outside).unwrap();
    fs::write(outside.join("sentinel"), vec![0; 4096]).unwrap();
    let link = f.store.join("git").join("e".repeat(64));
    symlink(&outside, &link).unwrap();
    symlink(&outside, orphan.join("link")).unwrap();
    let jit = f.home.join(".cache/brass/jit");
    fs::create_dir_all(&jit).unwrap();
    fs::write(jit.join("sentinel"), "jit").unwrap();

    let info = f.success(&["cache", "info"], true);
    assert_eq!(info.matches("Package store:").count(), 1);
    for expected in [
        "Total entries: 5",
        "Stale staging directories: 1",
        "Stale staging size: 3 B (3 bytes)",
        "parent (git https://example.invalid/parent.git @ abc123)",
        "child (tarball https://example.invalid/b.tar.gz",
        "leaf (git https://example.invalid/leaf.git @ v1)",
        &format!("{c}: 2 KiB (2048 bytes)"),
    ] {
        assert!(info.contains(expected), "missing {expected:?}: {info}");
    }
    let outside_info = f.success(&["cache", "info"], false);
    assert!(!outside_info.contains("parent ("));
    assert!(outside_info.contains("Total entries: 5"));
    let help = f.success(&["help"], false);
    assert!(help.contains("cache info") && help.contains("cache clean [NAME...]"));

    // Selection is fully validated before the first removal, including missing entries.
    f.failure(&["cache", "clean", "parent", "unknown"], true, "`unknown`");
    f.failure(
        &["cache", "clean", "parent", "missing"],
        true,
        "`missing` has no cached entry",
    );
    f.failure(
        &["cache", "clean", "parent"],
        false,
        "requires package.toml",
    );
    assert!(parent.is_dir());
    manifest(
        &local,
        &format!("child = {{ tarball = \"https://example.invalid/a.tar.gz\", hash = \"{a}\" }}"),
    );
    f.failure(
        &["cache", "clean", "parent", "child"],
        true,
        "`child` maps to more than one source",
    );
    assert!(parent.is_dir() && child.is_dir() && archive.is_dir());
    manifest(
        &local,
        "leaf = { git = \"https://example.invalid/leaf.git\", rev = \"v1\" }",
    );
    let path = f.success(&["cache", "clean", "local"], true);
    assert!(path.contains("local: path dependency (nothing cached)"));
    assert!(path.contains("Removed entries: 0"));
    assert!(local.is_dir());
    let named = f.success(&["cache", "clean", "child", "leaf", "child"], true);
    assert!(named.contains("Removed entries: 2"));
    assert!(!child.exists() && !leaf.exists());
    assert!(parent.is_dir() && archive.is_dir() && stale.is_dir());
    fs::remove_file(parent.join("package.toml")).unwrap();
    f.failure(
        &["cache", "clean", "parent", "child"],
        true,
        "`child` (local manifests only)",
    );
    assert!(parent.is_dir());

    let clean = f.success(&["cache", "clean"], false);
    assert!(clean.contains("Removed entries: 3"), "{clean}");
    assert!(clean.contains("Removed stale staging directories: 1"));
    for path in [&parent, &archive, &orphan, &stale] {
        assert!(!path.exists(), "{} survived", path.display());
    }
    for path in [
        &f.store,
        &fresh,
        &active,
        &foreign,
        &malformed,
        &link,
        &outside.join("sentinel"),
        &jit.join("sentinel"),
        &f.store.join("git").join("d".repeat(64)),
    ] {
        assert!(path.exists(), "{} removed", path.display());
    }
    assert!(
        f.success(&["cache", "clean"], false)
            .contains("Removed entries: 0")
    );
}

#[test]
fn missing_and_unmanaged_store_roots_are_never_created_or_followed() {
    let f = Fixture::new();
    assert!(
        f.success(&["cache", "info"], false)
            .contains("Total entries: 0")
    );
    assert!(
        f.success(&["cache", "clean"], false)
            .contains("Removed entries: 0")
    );
    assert!(!f.store.exists());
    let outside = f.root.join("outside");
    let payload = outside.join("git").join("a".repeat(64));
    fs::create_dir_all(&payload).unwrap();
    fs::create_dir_all(f.store.parent().unwrap()).unwrap();
    symlink(&outside, &f.store).unwrap();
    assert!(
        f.success(&["cache", "clean"], false)
            .contains("Removed entries: 0")
    );
    assert!(payload.exists());
    fs::remove_file(&f.store).unwrap();
    fs::create_dir(&f.store).unwrap();
    symlink(outside.join("git"), f.store.join("git")).unwrap();
    assert!(
        f.success(&["cache", "clean"], false)
            .contains("Removed entries: 0")
    );
    assert!(payload.exists());
    fs::write(f.store.join("tarball"), "file").unwrap();
    f.failure(
        &["cache", "clean"],
        false,
        "package cache path is not a directory",
    );
    assert!(payload.exists());
}
