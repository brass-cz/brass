//! End-to-end over a native plugin: build the fixture cdylib, place it as a
//! plugin module next to a program, and run the program on both back ends.

#![cfg(not(target_family = "wasm"))]

use std::fs;
use std::path::PathBuf;
use std::process::Command;

/// The test program: every supported value shape crosses the plugin boundary
/// (including arrays, in both directions and nested), plus the fallible
/// function's Ok and Err paths.
const MAIN_PP: &str = r#"import plugins.mathx.{ add, repeat, checked_div, byte_len, scale, is_even, undocumented, join, split, row_lengths }

println(add(40, 2))
println(repeat("ho", 3))
println(checked_div(10, 2)!)
match checked_div(1, 0) {
    Ok { value } => println("ok {value}"),
    Err { error } => println("err {error}"),
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
println("done")
"#;

const EXPECTED: &str =
    "42\nho ho ho\n5\nerr division by zero\n3\ntrue\nfalse\na-b-c\nxy 2\n2 0\ndone\n";

/// Lay out `<tmp>/main.pp` with the fixture library at
/// `<tmp>/plugins/mathx.<dll>`, so `import plugins.mathx` resolves to it.
fn project_dir() -> PathBuf {
    let lib = prepoly_plugin_host::fixture::build_testlib();
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("plugin_import");
    let plugins = dir.join("plugins");
    fs::create_dir_all(&plugins).expect("create project dirs");
    fs::write(dir.join("main.pp"), MAIN_PP).expect("write main.pp");
    let target = plugins.join(format!("mathx{}", std::env::consts::DLL_SUFFIX));
    fs::copy(&lib, &target).expect("place the plugin library");
    dir
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
    let dir = project_dir();
    let (ok, stdout, stderr) = run(&[], &dir);
    assert!(ok, "jit run failed:\n{stderr}");
    assert_eq!(stdout, EXPECTED, "stderr:\n{stderr}");
}

/// The REPL interpreter marshals the same calls through the shared host.
#[test]
fn plugin_import_runs_on_the_interpreter() {
    let dir = project_dir();
    let (ok, stdout, stderr) = run(&["repl"], &dir);
    assert!(ok, "interpreter run failed:\n{stderr}");
    assert_eq!(stdout, EXPECTED, "stderr:\n{stderr}");
}
