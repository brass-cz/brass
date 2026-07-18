//! End-to-end coverage for the package manager's Git cache. The repository is
//! local so the test checks URL preservation and checkout location without a
//! network dependency.

#![cfg(all(feature = "jit", not(target_family = "wasm")))]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn std_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std")
}

fn std_package_env() -> String {
    format!(
        "std={}",
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .display()
    )
}

fn run(command: &mut Command) {
    let status = command.status().expect("run command");
    assert!(status.success(), "command failed with {status}");
}

/// `git_clone` must pass the original repository path to Git and run checkout
/// inside the cached clone. A second call reuses the completed checkout.
#[test]
fn git_dependencies_clone_and_checkout_in_the_cache() {
    for (package, library) in [
        ("brass_lib_process", "process"),
        ("brass_lib_path", "path"),
        ("brass_lib_fs", "fs"),
        ("brass_lib_hash", "hash"),
        ("brass_lib_env", "env"),
    ] {
        brass_plugin_host::fixture::install_plugin(package, library, &std_root());
    }

    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock is after the Unix epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "brass_package_manager-{}-{nonce}",
        std::process::id()
    ));
    let repo = dir.join("source");
    let home = dir.join("home");
    std::fs::create_dir_all(&repo).expect("create source repository");
    std::fs::create_dir_all(&home).expect("create test home");
    run(Command::new("git").arg("init").arg(&repo));
    std::fs::write(repo.join("package.toml"), "fixture\n").expect("write fixture");
    run(Command::new("git").arg("-C").arg(&repo).args([
        "-c",
        "user.name=Brass Test",
        "-c",
        "user.email=brass@example.invalid",
        "add",
        "package.toml",
    ]));
    run(Command::new("git").arg("-C").arg(&repo).args([
        "-c",
        "user.name=Brass Test",
        "-c",
        "user.email=brass@example.invalid",
        "-c",
        "commit.gpgsign=false",
        "commit",
        "-m",
        "fixture",
    ]));
    let revision = Command::new("git")
        .arg("-C")
        .arg(&repo)
        .args(["rev-parse", "HEAD"])
        .output()
        .expect("read revision");
    assert!(revision.status.success());
    let revision = String::from_utf8(revision.stdout)
        .expect("Git revision is UTF-8")
        .trim()
        .to_string();

    let program = dir.join("clone.cz");
    std::fs::write(
        &program,
        "import std.package_manager.resolve.git_clone\nimport std.env.args\n\nconst argv = args()\nprintln(git_clone(argv[1], argv[2])!.to_string())\nprintln(git_clone(argv[1], argv[2])!.to_string())\n",
    )
    .expect("write package-manager program");
    let output = Command::new(env!("CARGO_BIN_EXE_brass"))
        .env("BRASS_CACHE", "off")
        .env("BRASS_PACKAGES", std_package_env())
        .env("HOME", &home)
        .arg(&program)
        .arg(&repo)
        .arg(&revision)
        .output()
        .expect("run package manager");
    assert!(
        output.status.success(),
        "package manager failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let paths: Vec<&str> = std::str::from_utf8(&output.stdout)
        .expect("package-manager output is UTF-8")
        .lines()
        .collect();
    assert_eq!(paths.len(), 2);
    assert_eq!(paths[0], paths[1], "the second call should reuse the cache");
    let checkout = Path::new(paths[0]);
    assert!(checkout.join(".git").is_dir());
    let head = Command::new("git")
        .arg("-C")
        .arg(checkout)
        .args(["rev-parse", "HEAD"])
        .output()
        .expect("read cached revision");
    assert!(head.status.success());
    assert_eq!(String::from_utf8_lossy(&head.stdout).trim(), revision);

    // A transitive path is relative to the package that declares it, not to
    // the root command's working directory.
    let path_root = dir.join("path-root");
    let outer = dir.join("path-outer");
    let inner = outer.join("nested");
    std::fs::create_dir_all(&path_root).expect("create path root");
    std::fs::create_dir_all(&inner).expect("create nested dependency");
    std::fs::write(
        path_root.join("package.toml"),
        "[package]\nname = \"root\"\nauthor = \"\"\nlicense = \"MIT\"\n\n[dependencies]\nouter = { path = \"../path-outer\" }\n",
    )
    .expect("write root manifest");
    std::fs::write(
        outer.join("package.toml"),
        "[package]\nname = \"outer\"\nauthor = \"\"\nlicense = \"MIT\"\n\n[dependencies]\ninner = { path = \"nested\" }\n",
    )
    .expect("write outer manifest");
    std::fs::write(
        inner.join("package.toml"),
        "[package]\nname = \"inner\"\nauthor = \"\"\nlicense = \"MIT\"\n\n[dependencies]\n",
    )
    .expect("write inner manifest");
    let resolver = path_root.join("resolve_paths.cz");
    std::fs::write(
        &resolver,
        "import std.fs.read_file\nimport std.package_manager.manifest.Manifest\nimport std.package_manager.resolve.resolve_deps\n\nconst manifest = Manifest.parse(read_file(\"package.toml\")!)!\nfor [name, path] in resolve_deps(manifest.dependencies)!.pairs() {\n    println(\"{name}={path}\")\n}\n",
    )
    .expect("write path resolver");
    let resolved = Command::new(env!("CARGO_BIN_EXE_brass"))
        .current_dir(&path_root)
        .env("BRASS_CACHE", "off")
        .env("BRASS_PACKAGES", std_package_env())
        .env("HOME", &home)
        .arg(&resolver)
        .output()
        .expect("resolve path dependencies");
    assert!(
        resolved.status.success(),
        "path resolution failed:\n{}",
        String::from_utf8_lossy(&resolved.stderr)
    );
    let resolved = String::from_utf8(resolved.stdout).expect("resolved paths are UTF-8");
    assert!(
        resolved
            .lines()
            .any(|line| line == format!("outer={}", outer.display())),
        "missing outer dependency in {resolved:?}"
    );
    assert!(
        resolved
            .lines()
            .any(|line| line == format!("inner={}", inner.display())),
        "missing inner dependency in {resolved:?}"
    );

    // Scaffolding refuses to overwrite an existing destination, validates the
    // package's importable name, and serves explicit help without a manifest.
    let scaffold = dir.join("scaffold");
    std::fs::create_dir_all(&scaffold).expect("create scaffold directory");
    let launcher = dir.join("czpm_test.cz");
    std::fs::write(
        &launcher,
        "import std.package_manager.exec.main\n\nmain()!\n",
    )
    .expect("write czpm launcher");
    let czpm = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_brass"))
            .current_dir(&scaffold)
            .env("BRASS_PACKAGES", std_package_env())
            .env("HOME", &home)
            .arg(&launcher)
            .args(args)
            .output()
            .expect("run czpm")
    };
    let help = czpm(&["--help"]);
    assert!(help.status.success());
    assert!(String::from_utf8_lossy(&help.stdout).contains("Usage:"));
    let created = czpm(&["new", "app"]);
    assert!(
        created.status.success(),
        "scaffold failed:\n{}",
        String::from_utf8_lossy(&created.stderr)
    );
    let manifest_path = scaffold.join("app/package.toml");
    std::fs::write(&manifest_path, "sentinel\n").expect("replace fixture manifest");
    let repeated = czpm(&["new", "app"]);
    assert!(
        !repeated.status.success(),
        "existing package was overwritten"
    );
    assert_eq!(
        std::fs::read_to_string(&manifest_path).expect("read protected manifest"),
        "sentinel\n"
    );
    let invalid = czpm(&["new", "bad-name"]);
    assert!(
        !invalid.status.success(),
        "invalid package name was accepted"
    );
    assert!(!scaffold.join("bad-name").exists());

    // A package's own name is not an import segment (a depender names the
    // package with its own dependency key), so a hyphenated name still runs,
    // locating its entry file. `run` spawns `brass` by name, hence the PATH.
    let hyphen = dir.join("hyphen");
    std::fs::create_dir_all(&hyphen).expect("create hyphenated package");
    std::fs::write(
        hyphen.join("package.toml"),
        "[package]\nname = \"my-app\"\nauthor = \"\"\nlicense = \"MIT\"\n\n[dependencies]\n",
    )
    .expect("write hyphenated manifest");
    std::fs::write(hyphen.join("my-app.cz"), "println(\"hyphen ok\")\n")
        .expect("write hyphenated entry");
    let exe_dir = Path::new(env!("CARGO_BIN_EXE_brass"))
        .parent()
        .expect("brass binary directory");
    let path_env = format!(
        "{}:{}",
        exe_dir.display(),
        std::env::var("PATH").unwrap_or_default()
    );
    let ran = Command::new(env!("CARGO_BIN_EXE_brass"))
        .current_dir(&hyphen)
        .env("BRASS_PACKAGES", std_package_env())
        .env("HOME", &home)
        .env("PATH", &path_env)
        .arg(&launcher)
        .args(["run"])
        .output()
        .expect("run hyphenated package");
    assert!(
        ran.status.success(),
        "hyphenated package name failed to run:\n{}",
        String::from_utf8_lossy(&ran.stderr)
    );
    assert!(
        String::from_utf8_lossy(&ran.stdout).contains("hyphen ok"),
        "entry did not run: {:?}",
        String::from_utf8_lossy(&ran.stdout)
    );

    // Dependency names ARE import segments and stay identifier-only, and the
    // manifest error must surface its own message through czpm's file-context
    // wrapper rather than being replaced by it.
    std::fs::write(
        hyphen.join("package.toml"),
        "[package]\nname = \"my-app\"\nauthor = \"\"\nlicense = \"MIT\"\n\n[dependencies]\nbad-dep = { path = \"nowhere\" }\n",
    )
    .expect("write bad-dependency manifest");
    let refused = Command::new(env!("CARGO_BIN_EXE_brass"))
        .current_dir(&hyphen)
        .env("BRASS_PACKAGES", std_package_env())
        .env("HOME", &home)
        .env("PATH", &path_env)
        .arg(&launcher)
        .args(["run"])
        .output()
        .expect("run with a bad dependency name");
    assert!(
        !refused.status.success(),
        "bad dependency name was accepted"
    );
    let stderr = String::from_utf8_lossy(&refused.stderr);
    assert!(
        stderr.contains("is not a legal identifier"),
        "the manifest error's cause was swallowed:\n{stderr}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
