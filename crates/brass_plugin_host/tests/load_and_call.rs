//! End-to-end over a real cdylib: build the fixture plugin, dlopen it, read
//! its manifest, and call through the C ABI.

#![cfg(not(target_family = "wasm"))]

use std::fs;
use std::path::PathBuf;

use brass_plugin_host::{
    CallFailure, Value, ValueType, call, call_registered, fixture, load_manifest, register_plugin,
};

/// A private copy of `lib` under `<tmp>/<name>/`, so a test may delete or
/// overwrite it without disturbing the built artifact or another test.
fn private_copy(lib: &std::path::Path, name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(name);
    fs::create_dir_all(&dir).expect("create the test directory");
    let dest = dir.join(format!("plug{}", std::env::consts::DLL_SUFFIX));
    fs::copy(lib, &dest).expect("copy the library");
    dest
}

/// The manifest carries every function with its doc comment, parameter
/// names/types, return type, and fallibility.
#[test]
fn manifest_reflects_the_fixture() {
    let lib = fixture::build_testlib();
    let manifest = load_manifest(&lib).expect("load fixture manifest");

    let add = manifest.function("add").expect("add");
    assert_eq!(add.doc.as_deref(), Some("Adds two integers."));
    assert_eq!(
        add.params,
        vec![
            ("a".to_string(), ValueType::Int),
            ("b".to_string(), ValueType::Int)
        ]
    );
    assert_eq!((&add.ret, add.fallible), (&ValueType::Int, false));

    let div = manifest.function("checked_div").expect("checked_div");
    assert!(div.fallible, "Result return marks the function fallible");

    let undoc = manifest.function("undocumented").expect("undocumented");
    assert_eq!(undoc.doc, None);
    assert_eq!((&undoc.ret, undoc.params.len()), (&ValueType::Void, 0));

    // Arrays are ordinary types: a parameter, a return, and nested.
    let split = manifest.function("split").expect("split");
    assert_eq!(split.ret, ValueType::array_of(ValueType::Str));
    let rows = manifest.function("row_lengths").expect("row_lengths");
    assert_eq!(
        rows.params[0].1,
        ValueType::array_of(ValueType::array_of(ValueType::Str))
    );
    assert_eq!(rows.ret, ValueType::array_of(ValueType::Int));

    // Loading again returns the cached manifest (same library handle).
    let again = load_manifest(&lib).expect("cached load");
    assert_eq!(again.functions.len(), manifest.functions.len());
}

/// Values of every supported type cross the boundary in both directions, and
/// a fallible function's error surfaces as a plugin failure.
#[test]
fn calls_cross_the_boundary() {
    let lib = fixture::build_testlib();

    let got = call(&lib, "add", &[Value::Int(40), Value::Int(2)]).expect("add");
    assert_eq!(got, Value::Int(42));

    let got = call(&lib, "repeat", &[Value::Str("ho".into()), Value::Int(3)]).expect("repeat");
    assert_eq!(got, Value::Str("ho ho ho".into()));

    let got = call(&lib, "byte_len", &[Value::Bytes(vec![1, 2, 3])]).expect("byte_len");
    assert_eq!(got, Value::Int(3));

    // Arrays cross both ways, at any nesting depth.
    let parts = Value::Array(vec![Value::Str("a".into()), Value::Str("b".into())]);
    let got = call(&lib, "join", &[parts, Value::Str("-".into())]).expect("join");
    assert_eq!(got, Value::Str("a-b".into()));

    let got = call(
        &lib,
        "split",
        &[Value::Str("x,y".into()), Value::Str(",".into())],
    )
    .expect("split");
    assert_eq!(
        got,
        Value::Array(vec![Value::Str("x".into()), Value::Str("y".into())])
    );

    let rows = Value::Array(vec![
        Value::Array(vec![Value::Str("a".into()), Value::Str("b".into())]),
        Value::Array(vec![]),
    ]);
    let got = call(&lib, "row_lengths", &[rows]).expect("row_lengths");
    assert_eq!(got, Value::Array(vec![Value::Int(2), Value::Int(0)]));

    let got = call(&lib, "scale", &[Value::Float(1.5), Value::Float(4.0)]).expect("scale");
    assert_eq!(got, Value::Float(6.0));

    let got = call(&lib, "is_even", &[Value::Int(7)]).expect("is_even");
    assert_eq!(got, Value::Bool(false));

    let got = call(&lib, "undocumented", &[]).expect("undocumented");
    assert_eq!(got, Value::Void);

    match call(&lib, "checked_div", &[Value::Int(1), Value::Int(0)]) {
        Err(CallFailure::Plugin(msg)) => assert_eq!(msg, "division by zero"),
        other => panic!("expected a plugin error, got {other:?}"),
    }

    match call(&lib, "no_such_fn", &[]) {
        Err(CallFailure::Host(msg)) => assert!(msg.contains("no function"), "{msg}"),
        other => panic!("expected a host error, got {other:?}"),
    }
}

/// Logical dispatch resolves through the process registry, while a missing
/// identity is a distinct fatal handoff failure that names that identity.
#[test]
fn logical_identity_dispatches_and_reports_missing_registration() {
    let lib = fixture::build_testlib();
    register_plugin("tests.mathx", &lib).expect("register fixture");
    assert_eq!(
        call_registered("tests.mathx", "add", &[Value::Int(40), Value::Int(2)])
            .expect("logical call"),
        Value::Int(42)
    );

    match call_registered("tests.missing_plugin", "add", &[]) {
        Err(CallFailure::Unregistered(message)) => {
            assert!(message.contains("tests.missing_plugin"), "{message}")
        }
        other => panic!("expected an unregistered identity, got {other:?}"),
    }
}

/// A running program pins the library it was compiled against: once loaded,
/// `call` answers from the cache without a filesystem syscall, so a cleanup
/// step or a rebuild that deletes-then-recreates the `.so` cannot abort it.
#[test]
fn calls_survive_the_library_file_disappearing() {
    let lib = private_copy(&fixture::build_testlib(), "pinned_plugin");
    assert_eq!(
        call(&lib, "add", &[Value::Int(40), Value::Int(2)]).expect("first call"),
        Value::Int(42)
    );

    fs::remove_file(&lib).expect("delete the library mid-run");
    assert_eq!(
        call(&lib, "add", &[Value::Int(1), Value::Int(1)]).expect("call after deletion"),
        Value::Int(2)
    );
}

/// The front end revalidates: a language server or REPL that outlives a plugin
/// rebuild must see the new manifest, not the one it read at startup. A
/// manifest already handed out keeps describing the build it came from (it is
/// host-owned data), and a later call reaches the new code.
#[test]
fn load_manifest_sees_a_rebuilt_library() {
    let lib = private_copy(&fixture::build_testlib(), "revalidated_plugin");
    let before = load_manifest(&lib).expect("initial manifest");
    assert!(before.function("add").is_some());
    assert!(before.function("extra").is_none());

    // An unchanged file is not reloaded: the same manifest object comes back.
    let cached = load_manifest(&lib).expect("cached manifest");
    assert!(
        std::sync::Arc::ptr_eq(&before, &cached),
        "no needless reload"
    );

    // Swap through a rename, the way a linker installs a rebuilt library:
    // writing over the mapped file in place would fault the old mapping.
    let staged = lib.with_extension("new");
    fs::copy(fixture::build_altlib(), &staged).expect("stage the rebuilt library");
    fs::rename(&staged, &lib).expect("install the rebuilt library");

    let after = load_manifest(&lib).expect("manifest after the rebuild");
    assert!(
        after.function("extra").is_some(),
        "the new function is seen"
    );
    // The old manifest is still readable, and still describes the old build.
    assert!(before.function("extra").is_none());

    // Calls now reach the new code (the stale entry was purged, not just the
    // canonical key), and the superseded library was retired, not unloaded.
    assert_eq!(call(&lib, "extra", &[]).expect("extra"), Value::Int(7));
}

/// A plugin whose registration panics is a load error, not a process abort:
/// `load_manifest` runs inside the compiler and the language server, and the
/// raw ABI's only failure channel is a null manifest. Retrying is well defined
/// (the panicking initializer leaves the plugin's `OnceLock` empty).
#[test]
fn a_panicking_registration_reports_a_load_error() {
    let lib = fixture::build_faultylib();
    for _ in 0..2 {
        match load_manifest(&lib) {
            Err(msg) => assert!(msg.contains("failed to initialize"), "{msg}"),
            Ok(_) => panic!("a panicking `entry` must not yield a manifest"),
        }
    }
}
