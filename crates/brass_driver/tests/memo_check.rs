//! The elaboration memo is an optimization only: replaying a memoized call-site
//! elaboration must reach the same verdict as elaborating the body again.
//! `BRASS_MEMO_CHECK=1` bypasses every memo hit (and, in a debug build,
//! asserts that the replay and the re-elaboration agree), so each case here is
//! checked both ways and the two runs must print the same diagnostics with the
//! same exit status.

mod support;

use std::path::{Path, PathBuf};

fn e2e_case(rel: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../e2e_tests")
        .join(rel)
}

/// Run `brass check` on `case`, with or without the memo bypass, and return
/// (success, stdout + stderr).
fn check(case: &Path, memo_check: bool) -> (bool, String) {
    let mut command = support::brass_command(env!("CARGO_BIN_EXE_brass"));
    command.arg("check").arg(case);
    if memo_check {
        command.env("BRASS_MEMO_CHECK", "1");
    } else {
        command.env_remove("BRASS_MEMO_CHECK");
    }
    let out = command.output().expect("spawn brass");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    (out.status.success(), combined)
}

#[test]
fn memo_bypass_never_changes_a_verdict() {
    // Each case calls one body more than once in a way a replay could get
    // wrong: a result that IS a global's type, a call inside a type-test probe
    // that the checker undoes, and a closure application whose effect on a
    // global must outlive the speculative check of the closure body.
    let rejected = [
        "types/memo_shared_global_rejected.cz",
        "types/memo_type_test_probe_rejected.cz",
        "closure/closure_application_pins_global_rejected.cz",
    ];
    let accepted = [
        "closure/closure_application_pins_global.cz",
        "collections/global_map_pinned_by_functions.cz",
        "types/fallible_chain_depth.cz",
    ];
    for (cases, should_pass) in [(&rejected[..], false), (&accepted[..], true)] {
        for rel in cases {
            let case = e2e_case(rel);
            let memoized = check(&case, false);
            let bypassed = check(&case, true);
            assert_eq!(
                memoized, bypassed,
                "{rel}: the memo bypass changed the verdict"
            );
            assert_eq!(
                memoized.0, should_pass,
                "{rel}: unexpected verdict: {}",
                memoized.1
            );
        }
    }
}
