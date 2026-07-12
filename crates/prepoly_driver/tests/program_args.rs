//! End-to-end: everything after the program file on the driver's command
//! line reaches the program through the env library's `args()`, on both back
//! ends and regardless of the arguments' shape (flag-like, spaces, names of
//! driver subcommands).
//!
//! Kept out of `e2e.rs` deliberately: this file is its own test process, and
//! cargo runs test binaries one after another, so installing the plugins here
//! cannot race a case process of the other suite mapping a half-copied
//! library.

#![cfg(all(feature = "jit", not(target_family = "wasm")))]

use std::path::{Path, PathBuf};
use std::process::Command;

fn libraries_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../libraries")
}

/// Run `prepoly [repl] <program> <args...>` with `libraries/` on the include
/// path and return its stdout.
fn run_with_args(mode: Option<&str>, program: &Path, args: &[&str]) -> String {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_prepoly"));
    if let Some(mode) = mode {
        cmd.arg(mode);
    }
    let out = cmd
        .arg(program)
        .args(args)
        .env("PREPOLY_INCLUDE", libraries_root())
        .output()
        .expect("spawn prepoly");
    assert!(
        out.status.success(),
        "prepoly failed\nstderr:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

#[test]
fn trailing_arguments_reach_args() {
    // The env library's plugin, plus path: env.pp imports path.pp (for
    // `current_dir`), so loading the env module needs libpath present too.
    for (package, library) in [("prepoly_lib_env", "env"), ("prepoly_lib_path", "path")] {
        prepoly_plugin_host::fixture::install_plugin(package, library, &libraries_root());
    }

    let dir = std::env::temp_dir().join(format!("prepoly_program_args-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create the program dir");
    let program = dir.join("echo_args.pp");
    std::fs::write(
        &program,
        "import env.{ args }\n\nfun main() {\n    for a in args() {\n        println(a)\n    }\n}\n",
    )
    .expect("write the program");

    // Everything after the file is the program's, verbatim: flag-shaped
    // arguments, spaces, and words that name driver subcommands must not be
    // consumed by the driver's own CLI.
    let args = ["alpha", "--beta", "with space", "check", "repl"];
    let mut expected = format!("{}\n", program.display());
    for a in args {
        expected.push_str(a);
        expected.push('\n');
    }

    // The default runtime (a bare file argument) and the REPL interpreter
    // (`repl <file>`) publish the same vector.
    assert_eq!(run_with_args(None, &program, &args), expected);
    assert_eq!(run_with_args(Some("repl"), &program, &args), expected);

    let _ = std::fs::remove_dir_all(&dir);
}
