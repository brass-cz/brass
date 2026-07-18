//! End-to-end test: examples within the typed (Value-free) subset must run to
//! completion; every example must still type-check. The typed back end is the
//! only execution path (the boxed-Value back end has been removed), so examples
//! that still exercise runtime features outside that subset type-check but do not
//! run in this test.

use std::process::Command;

/// Examples the typed back end runs end to end.
const RUNNABLE: &[&str] = &[
    "examples/01_records.cz",
    "examples/02_sum_types.cz",
    "examples/03_interfaces.cz",
    "examples/04_sum_interface.cz",
    "examples/05_nullable_and_result.cz",
    "examples/06_structural_subtyping.cz",
    "examples/07_closures.cz",
    "examples/08_pattern_matching.cz",
    "examples/09_collections.cz",
    "examples/10_strings_and_conversions.cz",
    "examples/11_control_flow.cz",
    "examples/13_file_io.cz",
    "examples/14_type_safety.cz",
    "examples/15_numeric_conversions.cz",
    "examples/16_method_inference.cz",
    "examples/17_higher_order.cz",
    "examples/18_methods.cz",
    "examples/modules/main.cz",
];

/// Valid examples outside the typed runtime subset: they type-check but use
/// constructs the typed back end does not yet lower, so they do not run.
const TYPECHECK_ONLY: &[&str] = &["examples/12_concurrency.cz"];

fn all_examples() -> Vec<&'static str> {
    RUNNABLE.iter().chain(TYPECHECK_ONLY).copied().collect()
}

fn repo_root() -> String {
    // The driver manifest lives at crates/brass_driver; the repo root is two
    // levels up.
    format!("{}/../..", env!("CARGO_MANIFEST_DIR"))
}

#[test]
fn runnable_examples_run_successfully() {
    let bin = env!("CARGO_BIN_EXE_brass");
    let root = repo_root();
    for ex in RUNNABLE {
        let path = format!("{root}/{ex}");
        let out = Command::new(bin)
            .env("BRASS_CACHE", "off")
            .arg(&path)
            .env("BRASS_PACKAGES", format!("std={root}"))
            .output()
            .expect("spawn brass");
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
    let bin = env!("CARGO_BIN_EXE_brass");
    let root = repo_root();
    for ex in all_examples() {
        let path = format!("{root}/{ex}");
        let out = Command::new(bin)
            .env("BRASS_CACHE", "off")
            .arg("check")
            .arg(&path)
            .env("BRASS_PACKAGES", format!("std={root}"))
            .output()
            .expect("spawn brass");
        assert!(
            out.status.success(),
            "example {ex} did not type-check\nstderr:\n{}",
            String::from_utf8_lossy(&out.stderr),
        );
    }
}
