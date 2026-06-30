//! End-to-end test: examples within the typed (Value-free) subset must run to
//! completion; every example must still type-check. The typed back end is the
//! only execution path (the boxed-Value back end has been removed), so examples
//! that still exercise runtime features outside that subset type-check but do not
//! run in this test.

use std::process::Command;

/// Examples the typed back end runs end to end.
const RUNNABLE: &[&str] = &[
    "examples/01_records.pp",
    "examples/02_sum_types.pp",
    "examples/03_interfaces.pp",
    "examples/04_sum_interface.pp",
    "examples/05_nullable_and_result.pp",
    "examples/06_structural_subtyping.pp",
    "examples/07_closures.pp",
    "examples/08_pattern_matching.pp",
    "examples/09_collections.pp",
    "examples/10_strings_and_conversions.pp",
    "examples/11_control_flow.pp",
    "examples/13_file_io.pp",
    "examples/14_type_safety.pp",
    "examples/15_numeric_conversions.pp",
    "examples/16_method_inference.pp",
    "examples/17_higher_order.pp",
    "examples/18_ufcs.pp",
    "examples/modules/main.pp",
];

/// Valid examples outside the typed runtime subset: they type-check but use
/// constructs the typed back end does not yet lower, so they do not run.
const TYPECHECK_ONLY: &[&str] = &["examples/12_concurrency.pp"];

fn all_examples() -> Vec<&'static str> {
    RUNNABLE.iter().chain(TYPECHECK_ONLY).copied().collect()
}

fn repo_root() -> String {
    // The driver manifest lives at crates/prepoly_driver; the repo root is two
    // levels up.
    format!("{}/../..", env!("CARGO_MANIFEST_DIR"))
}

#[test]
fn runnable_examples_run_successfully() {
    let bin = env!("CARGO_BIN_EXE_prepoly");
    let root = repo_root();
    for ex in RUNNABLE {
        let path = format!("{root}/{ex}");
        let out = Command::new(bin)
            .arg(&path)
            .output()
            .expect("spawn prepoly");
        assert!(
            out.status.success(),
            "example {ex} failed (status {:?})\nstdout:\n{}\nstderr:\n{}",
            out.status.code(),
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr),
        );
    }
}

#[test]
fn all_examples_typecheck() {
    let bin = env!("CARGO_BIN_EXE_prepoly");
    let root = repo_root();
    for ex in all_examples() {
        let path = format!("{root}/{ex}");
        let out = Command::new(bin)
            .arg("check")
            .arg(&path)
            .output()
            .expect("spawn prepoly");
        assert!(
            out.status.success(),
            "example {ex} did not type-check\nstderr:\n{}",
            String::from_utf8_lossy(&out.stderr),
        );
    }
}
