//! End-to-end over a native plugin: build the fixture cdylib, place it as a
//! plugin module next to a program, and run the program on both back ends.

#![cfg(not(target_family = "wasm"))]

use std::fs;
use std::path::PathBuf;
use std::process::Command;

/// The test program: every supported value shape crosses the plugin boundary
/// (including arrays, in both directions and nested), plus the fallible
/// function's Ok and Err paths.
const MAIN_PP: &str = r#"import plugins.mathx.{ add, repeat, checked_div, byte_len, scale, is_even, undocumented, join, split, row_lengths, negate, match_, len_ }

println(add(40, 2))
println(repeat("ho", 3))
println(checked_div(10, 2)!)
match checked_div(1, 0) {
    Ok { value } => println("ok {value}"),
    // The payload is the prelude `Error` wrapping the plugin's message;
    // print the message so the expectation stays position-free.
    Err { error } => println("err {error.value}"),
}
println(byte_len(_string_bytes("abc")))
println(scale(1.5, 4.0) == 6.0)
println(is_even(7))
undocumented()

// A `string[]` in, a `string[]` out, and a `string[][]` in.
const words: string[] = ["a", "b", "c"]
println(join(words, "-"))
const parts = split("x,y", ",")
println("{parts[0]}{parts[1]} {len(parts)}")
const rows: string[][] = [["a", "b"], []]
const lengths = row_lengths(rows)
println("{lengths[0]} {lengths[1]}")

// A function documented with a nested block comment still imports.
println(negate(7))
// Plugin functions named after a Prepoly keyword and a runtime builtin import
// under a `_` suffix and dispatch to their own names.
println(match_(21))
println(len_("abcd"))
println("done")
"#;

const EXPECTED: &str =
    "42\nho ho ho\n5\nerr division by zero\n3\ntrue\nfalse\na-b-c\nxy 2\n2 0\n-7\n42\n4\ndone\n";

/// Lay out `<tmp>/<name>/main.pp` holding `src`, with the fixture library at
/// `<tmp>/<name>/plugins/mathx.<dll>`, so `import plugins.mathx` resolves to
/// it. Returns the project directory and the plugin library's path.
fn project_dir_with(name: &str, src: &str) -> (PathBuf, PathBuf) {
    let lib = prepoly_plugin_host::fixture::build_testlib();
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(name);
    let plugins = dir.join("plugins");
    fs::create_dir_all(&plugins).expect("create project dirs");
    fs::write(dir.join("main.pp"), src).expect("write main.pp");
    let target = plugins.join(format!("mathx{}", std::env::consts::DLL_SUFFIX));
    fs::copy(&lib, &target).expect("place the plugin library");
    (dir, target)
}

/// Each caller gets its own project directory: the tests run in parallel
/// threads, and re-copying the library into a shared path truncates a file
/// another test's prepoly process may have mapped (a SIGSEGV with no output).
fn project_dir(name: &str) -> PathBuf {
    project_dir_with(name, MAIN_PP).0
}

fn run(args: &[&str], dir: &PathBuf) -> (bool, String, String) {
    let bin = env!("CARGO_BIN_EXE_prepoly");
    let out = Command::new(bin)
        .args(args)
        .arg(dir.join("main.pp"))
        .output()
        .expect("spawn prepoly");
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

/// The JIT back end imports the plugin module and calls through the packed
/// slot ABI.
#[cfg(feature = "jit")]
#[test]
fn plugin_import_runs_on_the_jit() {
    let dir = project_dir("plugin_import_jit");
    let (ok, stdout, stderr) = run(&[], &dir);
    assert!(ok, "jit run failed:\n{stderr}");
    assert_eq!(stdout, EXPECTED, "stderr:\n{stderr}");
}

/// The REPL interpreter marshals the same calls through the shared host.
#[test]
fn plugin_import_runs_on_the_interpreter() {
    let dir = project_dir("plugin_import_repl");
    let (ok, stdout, stderr) = run(&["repl"], &dir);
    assert!(ok, "interpreter run failed:\n{stderr}");
    assert_eq!(stdout, EXPECTED, "stderr:\n{stderr}");
}

/// A hand-written dispatch call may name a return type the plugin does not
/// produce -- here `y` (`uint8[]`) for a function returning a string. The
/// checker cannot see through the library, so the runtime must refuse the
/// value instead of reading a string object's header as an array's.
#[cfg(feature = "jit")]
#[test]
fn plugin_return_type_mismatch_aborts_cleanly() {
    let (dir, lib) = project_dir_with("plugin_bad_return", "");
    let src = format!(
        "fun main() {{\n    let b = _plugin_call_y(\"{}\", \"repeat\", \"si:y\", \"a\", 1)\n    println(len(b))\n}}\n",
        lib.display()
    );
    fs::write(dir.join("main.pp"), src).expect("rewrite main.pp");

    let (ok, stdout, stderr) = run(&[], &dir);
    assert!(!ok, "the lying signature must abort; stdout:\n{stdout}");
    assert!(
        stderr.contains("plugin returned Str(\"a\") where Bytes was typed"),
        "stderr:\n{stderr}"
    );
}
