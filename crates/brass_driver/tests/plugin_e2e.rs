//! End-to-end over a native plugin: build the fixture cdylib, place it as a
//! plugin module next to a program, and run the program on both back ends.

#![cfg(not(target_family = "wasm"))]

mod support;

use std::fs;
use std::path::{Path, PathBuf};

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
// Plugin functions named after a Brass keyword and a runtime builtin import
// under a `_` suffix and dispatch to their own names.
println(match_(21))
println(len_("abcd"))
println("done")
"#;

const EXPECTED: &str =
    "42\nho ho ho\n5\nerr division by zero\n3\ntrue\nfalse\na-b-c\nxy 2\n2 0\n-7\n42\n4\ndone\n";

/// Lay out `<tmp>/<name>/main.cz` holding `src`, with the fixture library at
/// `<tmp>/<name>/plugins/mathx.<dll>`, so `import plugins.mathx` resolves to
/// it. Returns the project directory and the plugin library's path.
fn project_dir_with(name: &str, src: &str) -> (PathBuf, PathBuf) {
    let lib = brass_plugin_host::fixture::build_testlib();
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(name);
    let plugins = dir.join("plugins");
    fs::create_dir_all(&plugins).expect("create project dirs");
    fs::write(dir.join("main.cz"), src).expect("write main.cz");
    let target = plugins.join(format!("mathx{}", std::env::consts::DLL_SUFFIX));
    fs::copy(&lib, &target).expect("place the plugin library");
    (dir, target)
}

/// Each caller gets its own project directory: the tests run in parallel
/// threads, and re-copying the library into a shared path truncates a file
/// another test's Brass process may have mapped (a SIGSEGV with no output).
fn project_dir(name: &str) -> PathBuf {
    project_dir_with(name, MAIN_PP).0
}

fn run(args: &[&str], dir: &Path) -> (bool, String, String) {
    let bin = env!("CARGO_BIN_EXE_brass");
    let out = support::brass_command(bin)
        .args(args)
        .arg(dir.join("main.cz"))
        .output()
        .expect("spawn brass");
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
    let (dir, _) = project_dir_with("plugin_bad_return", "");
    let src = "import plugins.mathx\n\nfun main() {\n    let b = _plugin_call_y(\"plugins.mathx\", \"repeat\", \"si:y\", \"a\", 1)\n    println(len(b))\n}\n";
    fs::write(dir.join("main.cz"), src).expect("rewrite main.cz");

    let (ok, stdout, stderr) = run(&[], &dir);
    assert!(!ok, "the lying signature must abort; stdout:\n{stdout}");
    assert!(
        stderr.contains("plugin returned Str(\"a\") where Bytes was typed"),
        "stderr:\n{stderr}"
    );
}

/// A logical identity absent from the front-end registry is a fatal handoff
/// error on both execution back ends, even though the builtin is fallible.
#[test]
fn missing_logical_plugin_registration_is_fatal_on_both_backends() {
    let (dir, _) = project_dir_with("plugin_missing_registration", "");
    fs::write(
        dir.join("main.cz"),
        "fun main() {\n    let ignored = _plugin_fcall_i(\"plugins.not_imported\", \"add\", \"ii:i!\", 1, 2)\n    println(ignored)\n}\n",
    )
    .expect("write missing-registration program");

    for args in [&[][..], &["repl"][..]] {
        let (ok, stdout, stderr) = run(args, &dir);
        assert!(!ok, "missing registration must abort; stdout:\n{stdout}");
        assert!(
            stderr.contains("plugin `plugins.not_imported` is not registered"),
            "stderr:\n{stderr}"
        );
    }
}

/// The release layout discovers `std` from the running binary, native plugin
/// libraries included: `bin/brass` resolves `std.mathx` to the library in the
/// sibling `std/` directory with no environment setup.
#[test]
fn distributed_std_plugin_resolves_beside_the_binary() {
    let dist = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("plugin_distribution");
    let _ = fs::remove_dir_all(&dist);
    fs::create_dir_all(dist.join("bin")).expect("create distribution bin");
    fs::create_dir_all(dist.join("std")).expect("create distribution std");
    fs::copy(env!("CARGO_BIN_EXE_brass"), dist.join("bin/brass")).expect("copy distributed driver");
    fs::write(
        dist.join("bin/czpm"),
        "import std.mathx.{ add }\nprintln(add(40, 2))\n",
    )
    .expect("write distributed entry");
    let plugin = dist.join("std").join(format!(
        "{}mathx{}",
        std::env::consts::DLL_PREFIX,
        std::env::consts::DLL_SUFFIX
    ));
    fs::copy(brass_plugin_host::fixture::build_testlib(), &plugin)
        .expect("copy distributed plugin");

    // A parallel test can briefly inherit the just-closed copy handle between
    // fork and exec on Linux; retry only that transient ETXTBSY.
    let out = (0..50)
        .find_map(|_| {
            match support::brass_command(dist.join("bin/brass"))
                .arg(dist.join("bin/czpm"))
                .output()
            {
                Ok(output) => Some(output),
                Err(error) if error.raw_os_error() == Some(26) => {
                    std::thread::sleep(std::time::Duration::from_millis(20));
                    None
                }
                Err(error) => panic!("run distributed driver: {error}"),
            }
        })
        .expect("distributed driver remained busy");
    assert!(
        out.status.success(),
        "distributed run failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout), "42\n");
}

/// A source module introduced at a plugin's import path outranks the plugin
/// library on the next run.
#[test]
fn source_module_shadows_plugin_at_the_same_path() {
    let (dir, _) = project_dir_with(
        "plugin_source_shadow",
        "import plugins.mathx.{ add }\nprintln(add(40, 2))\n",
    );
    let _ = fs::remove_file(dir.join("plugins/mathx.cz"));
    let (ok, stdout, stderr) = run(&["--eager"], &dir);
    assert!(ok, "cold run failed: {stdout}\n{stderr}");
    assert_eq!(stdout, "42\n");

    fs::write(
        dir.join("plugins/mathx.cz"),
        "fun add(a: int64, b: int64) -> int64 { return 99 }\n",
    )
    .expect("add shadowing source module");
    let (ok, stdout, stderr) = run(&["--eager"], &dir);
    assert!(ok, "shadowed run failed: {stdout}\n{stderr}");
    assert_eq!(stdout, "99\n", "the source module must outrank the plugin");
}
