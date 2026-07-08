mod manifest;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use clap::{Parser, Subcommand};

use manifest::{Dependency, Manifest};

#[derive(Parser)]
#[command(name = "ppm", about = "Prepoly package manager")]
struct Cli {
    #[command(subcommand)]
    command: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Create a new prepoly project in a new directory.
    New {
        /// The package name.
        name: String,
    },
    /// Initialize a prepoly project in the current directory.
    Init {
        /// The package name.
        name: String,
    },
    /// Type-check the current package.
    Check,
    /// Run the current package.
    Run,
    /// Start the language server with package resolution.
    Lsp,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match cli.command {
        Cmd::New { name } => cmd_new(&name),
        Cmd::Init { name } => scaffold_project(Path::new("."), &name),
        Cmd::Check => cmd_drive("check"),
        Cmd::Run => cmd_drive("run"),
        Cmd::Lsp => cmd_lsp(),
    }
}

/// `ppm new <name>`: create a new directory and scaffold the project inside it.
fn cmd_new(name: &str) -> ExitCode {
    let dir = PathBuf::from(name);
    if let Err(e) = std::fs::create_dir_all(&dir) {
        eprintln!("error: cannot create directory `{}`: {e}", dir.display());
        return ExitCode::FAILURE;
    }
    scaffold_project(&dir, name)
}

/// Write the source directory, root file, and `package.toml` under `dir`.
fn scaffold_project(dir: &Path, name: &str) -> ExitCode {
    let src_dir = dir.join(name);
    if let Err(e) = std::fs::create_dir_all(&src_dir) {
        eprintln!(
            "error: cannot create source directory `{}/`: {e}",
            src_dir.display()
        );
        return ExitCode::FAILURE;
    }

    let root_file = dir.join(format!("{name}.pp"));
    if !root_file.exists()
        && let Err(e) = std::fs::write(&root_file, "")
    {
        eprintln!("error: cannot write `{}`: {e}", root_file.display());
        return ExitCode::FAILURE;
    }

    let manifest_path = dir.join("package.toml");
    if !manifest_path.exists() {
        let content = format!(
            r#"[package]
name = "{name}"
author = ""
license = "MIT"

[dependencies]
# mylib = {{ git = "https://github.com/user/mylib", hash = "<commit hash>" }}
# mylib = {{ path = "../mylib" }}
"#
        );
        if let Err(e) = std::fs::write(&manifest_path, content) {
            eprintln!("error: cannot write `{}`: {e}", manifest_path.display());
            return ExitCode::FAILURE;
        }
    }

    println!("created project `{name}`");
    ExitCode::SUCCESS
}

/// Read `package.toml`, fetch dependencies, and return the `PREPOLY_PACKAGES`
/// env-var value. Shared by `check`/`run`/`lsp`.
fn resolve_packages() -> Result<String, ExitCode> {
    let manifest = Manifest::load(Path::new("package.toml")).map_err(|e| {
        eprintln!("error: {e}");
        ExitCode::FAILURE
    })?;

    // The shared cache is only needed (and created) for git dependencies.
    let needs_cache = manifest
        .dependencies
        .values()
        .any(|d| matches!(d, Dependency::Git { .. }));
    let packages_dir = if needs_cache {
        Some(packages_root().map_err(|e| {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        })?)
    } else {
        None
    };

    let mut pkg_entries: BTreeMap<String, PathBuf> = BTreeMap::new();
    for (name, dep) in &manifest.dependencies {
        let dest = match dep {
            Dependency::Git { git, hash } => {
                let cache = packages_dir.as_ref().expect("created for git dependencies");
                fetch_git(name, git, hash, cache)?
            }
            Dependency::Path { path } => resolve_path_dep(name, path)?,
        };
        pkg_entries.insert(name.clone(), dest);
    }

    Ok(pkg_entries
        .iter()
        .map(|(name, path)| format!("{name}={}", path.display()))
        .collect::<Vec<_>>()
        .join(":"))
}

/// Clone-and-checkout a git dependency into the shared cache (a no-op when the
/// `name-git-hash` directory already exists) and return its directory.
fn fetch_git(name: &str, git: &str, hash: &str, packages_dir: &Path) -> Result<PathBuf, ExitCode> {
    let dir_name = format!("{name}-git-{hash}");
    let dest = packages_dir.join(&dir_name);
    if dest.exists() {
        return Ok(dest);
    }
    eprintln!("fetching {name} ({})...", &hash[..hash.len().min(8)]);
    let status = Command::new("git")
        .args(["clone", git, &dest.display().to_string()])
        .status();
    match status {
        Ok(s) if s.success() => {}
        Ok(s) => {
            eprintln!(
                "error: git clone failed for `{name}` (exit {})",
                s.code().unwrap_or(-1)
            );
            return Err(ExitCode::FAILURE);
        }
        Err(e) => {
            eprintln!("error: cannot run git: {e}");
            return Err(ExitCode::FAILURE);
        }
    }
    let status = Command::new("git")
        .args(["-C", &dest.display().to_string(), "checkout", hash])
        .status();
    match status {
        Ok(s) if s.success() => {}
        Ok(_) => {
            eprintln!("error: git checkout `{hash}` failed for `{name}`");
            return Err(ExitCode::FAILURE);
        }
        Err(e) => {
            eprintln!("error: cannot run git: {e}");
            return Err(ExitCode::FAILURE);
        }
    }
    Ok(dest)
}

/// Resolve a `{ path = "..." }` dependency against the project root (the
/// directory holding `package.toml`, which is the current directory for every
/// ppm command). The result is canonicalized so the absolute path stays valid
/// for whatever working directory the spawned tool ends up with.
fn resolve_path_dep(name: &str, path: &str) -> Result<PathBuf, ExitCode> {
    let dest = Path::new(path);
    match std::fs::canonicalize(dest) {
        Ok(p) if p.is_dir() => Ok(p),
        Ok(p) => {
            eprintln!(
                "error: path dependency `{name}`: `{}` is not a directory",
                p.display()
            );
            Err(ExitCode::FAILURE)
        }
        Err(e) => {
            eprintln!("error: path dependency `{name}`: cannot resolve `{path}`: {e}");
            Err(ExitCode::FAILURE)
        }
    }
}

/// Read `package.toml` in the current directory, fetch dependencies, set
/// `PREPOLY_PACKAGES`, and invoke `prepoly check` or `prepoly run` on the
/// root file.
fn cmd_drive(mode: &str) -> ExitCode {
    let manifest = match Manifest::load(Path::new("package.toml")) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::FAILURE;
        }
    };

    let env_val = match resolve_packages() {
        Ok(v) => v,
        Err(code) => return code,
    };

    let root_file = format!("{}.pp", manifest.package.name);

    let mut cmd = Command::new("prepoly");
    if mode == "check" {
        cmd.arg("check");
    }
    cmd.arg(&root_file);
    if !env_val.is_empty() {
        cmd.env("PREPOLY_PACKAGES", &env_val);
    }

    match cmd.status() {
        Ok(s) if s.success() => ExitCode::SUCCESS,
        Ok(s) => {
            let code: u8 = s.code().unwrap_or(1) as u8;
            ExitCode::from(code)
        }
        Err(e) => {
            eprintln!("error: cannot run prepoly: {e}");
            ExitCode::FAILURE
        }
    }
}

/// Start `prepoly-lsp`, with `PREPOLY_PACKAGES` set when the current
/// directory is a ppm project. Without a `package.toml` (the editor opened a
/// plain directory of .pp files) the server still starts, just without
/// package resolution: editors run this command at startup, so it must not
/// die where `prepoly-lsp` itself would come up.
fn cmd_lsp() -> ExitCode {
    let env_val = if Path::new("package.toml").exists() {
        match resolve_packages() {
            Ok(v) => v,
            Err(code) => return code,
        }
    } else {
        String::new()
    };

    let mut cmd = Command::new("prepoly-lsp");
    if !env_val.is_empty() {
        cmd.env("PREPOLY_PACKAGES", &env_val);
    }

    match cmd.status() {
        Ok(s) if s.success() => ExitCode::SUCCESS,
        Ok(s) => {
            let code: u8 = s.code().unwrap_or(1) as u8;
            ExitCode::from(code)
        }
        Err(e) => {
            eprintln!("error: cannot run prepoly-lsp: {e}");
            ExitCode::FAILURE
        }
    }
}

/// `$HOME/.prepoly/packages/`, created on demand.
fn packages_root() -> Result<PathBuf, String> {
    let home = std::env::var("HOME").map_err(|_| "HOME is not set".to_string())?;
    let dir = PathBuf::from(home).join(".prepoly").join("packages");
    std::fs::create_dir_all(&dir).map_err(|e| format!("cannot create `{}`: {e}", dir.display()))?;
    Ok(dir)
}
