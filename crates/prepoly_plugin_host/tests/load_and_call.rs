//! End-to-end over a real cdylib: build the fixture plugin, dlopen it, read
//! its manifest, and call through the C ABI.

#![cfg(not(target_family = "wasm"))]

use prepoly_plugin_host::{CallFailure, Value, ValueType, call, fixture, load_manifest};

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
