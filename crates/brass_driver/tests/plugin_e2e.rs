//! End-to-end over a native plugin: build the fixture cdylib, place it as a
//! plugin module next to a program, and run the program on both back ends.

#![cfg(not(target_family = "wasm"))]

use std::fs;
use std::path::{Path, PathBuf};
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
    let out = Command::new(bin)
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
    let (dir, lib) = project_dir_with("plugin_bad_return", "");
    let src = format!(
        "fun main() {{\n    let b = _plugin_call_y(\"{}\", \"repeat\", \"si:y\", \"a\", 1)\n    println(len(b))\n}}\n",
        lib.display()
    );
    fs::write(dir.join("main.cz"), src).expect("rewrite main.cz");

    let (ok, stdout, stderr) = run(&[], &dir);
    assert!(!ok, "the lying signature must abort; stdout:\n{stdout}");
    assert!(
        stderr.contains("plugin returned Str(\"a\") where Bytes was typed"),
        "stderr:\n{stderr}"
    );
}

/// A rebuilt plugin library must invalidate the analysis cache: the cached
/// wrapper module (and the signatures the program was checked against) came
/// from the OLD manifest, so a swapped library has to force fresh resolution
/// instead of the stale wrapper marshalling against the new native code.
#[test]
fn analysis_cache_misses_when_the_plugin_library_changes() {
    let (dir, target) = project_dir_with(
        "plugin_cache_swap",
        "import plugins.mathx.{ repeat }\nprintln(repeat(\"ha\", 2))\n",
    );
    let (ok, out, err) = run(&[], &dir);
    assert!(ok, "cold run: {out}\n{err}");
    assert_eq!(out, "ha ha\n");
    assert!(
        dir.join("main.czcache").is_file(),
        "a clean run writes the cache"
    );
    let (ok, out, _) = run(&[], &dir);
    assert!(ok && out == "ha ha\n", "warm run: {out}");

    // Swap in the alternative build, whose manifest lacks `repeat`.
    let alt = brass_plugin_host::fixture::build_altlib();
    fs::copy(&alt, &target).expect("swap the plugin library");
    let (ok, stdout, stderr) = run(&[], &dir);
    assert!(
        !ok,
        "the swapped library must be re-resolved, not served stale; stdout:\n{stdout}"
    );
    assert!(
        stderr.contains("repeat"),
        "the new manifest lacks `repeat`: {stderr}"
    );
}

/// A plugin-backed cache stores the canonical import and binary hash, not the
/// packing machine's library path. Moving the complete program therefore hits
/// the cache and dispatches through the library at its new location.
#[test]
fn analysis_cache_reanchors_a_relocated_plugin() {
    let (dir, plugin) = project_dir_with(
        "plugin_cache_relocate",
        "import plugins.mathx.{ add }\nprintln(add(40, 2))\n",
    );
    let cache = dir.join("main.czcache");
    let _ = fs::remove_file(&cache);

    // Eager checking deterministically publishes a complete cache.
    let (ok, stdout, stderr) = run(&["--eager"], &dir);
    assert!(ok, "cold run failed: {stdout}\n{stderr}");
    assert_eq!(stdout, "42\n");
    let plugin = plugin.canonicalize().expect("canonical plugin path");
    let cache_bytes = fs::read(&cache).expect("read generated cache");
    assert!(
        !cache_bytes
            .windows(plugin.as_os_str().as_encoded_bytes().len())
            .any(|window| window == plugin.as_os_str().as_encoded_bytes()),
        "cache embeds the packing location {}",
        plugin.display()
    );

    // Rename rather than copy so the old absolute path cannot accidentally
    // satisfy a stale wrapper or stamp.
    let moved = dir.with_file_name("plugin_cache_relocate_moved");
    let _ = fs::remove_dir_all(&moved);
    fs::rename(&dir, &moved).expect("move plugin program");
    let out = Command::new(env!("CARGO_BIN_EXE_brass"))
        .arg(moved.join("main.cz"))
        .env("BRASS_LOG", "brass::perf=debug")
        .output()
        .expect("run moved program");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "moved run failed: {stderr}");
    assert_eq!(String::from_utf8_lossy(&out.stdout), "42\n");
    assert!(stderr.contains("front/cache-hit"), "cache missed: {stderr}");
}

/// The release layout discovers `std` from the running binary. A cache packed
/// beside that binary must repeat the same resolution after the entire
/// toolchain is installed elsewhere.
#[test]
fn distributed_plugin_cache_survives_installation() {
    let dist = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("plugin_cache_distribution");
    let original = dist.join("packed");
    let installed = dist.join("installed");
    let _ = fs::remove_dir_all(&dist);
    fs::create_dir_all(original.join("bin")).expect("create distribution bin");
    fs::create_dir_all(original.join("std")).expect("create distribution std");
    fs::copy(env!("CARGO_BIN_EXE_brass"), original.join("bin/brass"))
        .expect("copy distributed driver");
    let entry = original.join("bin/czpm");
    fs::write(&entry, "import std.mathx.{ add }\nprintln(add(40, 2))\n")
        .expect("write distributed entry");
    let plugin = original.join("std").join(format!(
        "{}mathx{}",
        std::env::consts::DLL_PREFIX,
        std::env::consts::DLL_SUFFIX
    ));
    fs::copy(brass_plugin_host::fixture::build_testlib(), &plugin)
        .expect("copy distributed plugin");

    let run_at = |root: &Path, eager: bool| -> std::process::Output {
        // A parallel test can briefly inherit the just-closed copy handle
        // between fork and exec on Linux; retry only that transient ETXTBSY.
        for _ in 0..50 {
            let mut command = Command::new(root.join("bin/brass"));
            if eager {
                command.arg("--eager");
            }
            match command
                .arg(root.join("bin/czpm"))
                .env("BRASS_LOG", "brass::perf=debug")
                .output()
            {
                Ok(output) => return output,
                Err(error) if error.raw_os_error() == Some(26) => {
                    std::thread::sleep(std::time::Duration::from_millis(20));
                }
                Err(error) => panic!("run distributed driver: {error}"),
            }
        }
        panic!("distributed driver remained busy")
    };

    let out = run_at(&original, true);
    assert!(
        out.status.success(),
        "packed run failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout), "42\n");
    let plugin = plugin.canonicalize().expect("canonical packed plugin");
    let cache = fs::read(entry.with_extension("czcache")).expect("read packed cache");
    assert!(
        !cache
            .windows(plugin.as_os_str().as_encoded_bytes().len())
            .any(|window| window == plugin.as_os_str().as_encoded_bytes()),
        "distributed cache embeds {}",
        plugin.display()
    );

    // Installation removes the packing location, so a hit can only succeed by
    // resolving `std.mathx` relative to the installed binary.
    fs::rename(&original, &installed).expect("install distribution");
    let out = run_at(&installed, false);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "installed run failed: {stderr}");
    assert_eq!(String::from_utf8_lossy(&out.stdout), "42\n");
    assert!(stderr.contains("front/cache-hit"), "cache missed: {stderr}");
}

/// Resolution is authoritative on every hit. A source module introduced at
/// the same import path outranks the cached plugin and forces fresh analysis.
#[test]
fn analysis_cache_misses_when_source_shadows_plugin() {
    let (dir, _) = project_dir_with(
        "plugin_cache_source_shadow",
        "import plugins.mathx.{ add }\nprintln(add(40, 2))\n",
    );
    let _ = fs::remove_file(dir.join("plugins/mathx.cz"));
    let _ = fs::remove_file(dir.join("main.czcache"));
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
    assert_eq!(stdout, "99\n", "the cached plugin must not remain selected");
}
