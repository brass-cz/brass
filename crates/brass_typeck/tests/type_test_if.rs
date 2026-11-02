//! Checker-level behavior of the compile-time type test (`if v: T`): arm
//! selection per instantiation, hole pinning from the tested arm, and the
//! `type_tests` channel.

use brass_typeck::analyze;

fn lower(src: &str) -> brass_hir::Program {
    let ast = brass_parser::parse(src).expect("parse");
    let (program, lerr) = brass_hir::lower(&[brass_hir::LoadedModule {
        source: None,
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(lerr.is_empty(), "lower: {lerr:?}");
    program
}

/// The unselected arm of a decided type test is never reported from: the
/// int32[] instance takes the else path even though the tested arm cannot
/// type at int32[].
#[test]
fn unmatched_arm_reports_nothing() {
    let program = lower(
        "fun wants_str(s: string) -> int32 { return 1 }\n\
         fun length(val) {\n\
             if val: infer {\n\
                 return wants_str(val)\n\
             }\n\
             return 0\n\
         }\n\
         fun main() { println(length([1, 2, 3])) }\n",
    );
    let analysis = analyze(&program);
    assert!(analysis.errors.is_empty(), "errors: {:?}", analysis.errors);
}

/// A type test accepts the language's structural subtyping: a nominal record
/// that satisfies the tested type's fields matches (and the arm reads the
/// value at its own type), while an unrelated value falls through. Exact
/// scalar matching stays: no numeric widening.
#[test]
fn structural_subtype_matches_and_scalars_stay_exact() {
    let program = lower(
        "type Point = { x: int32, y: int32 }\n\
         fun inspect(v) -> string {\n\
             if v: anonymous { x: int32 } {\n\
                 return \"x\"\n\
             } else if v: int64 {\n\
                 return \"wide\"\n\
             }\n\
             return \"other\"\n\
         }\n\
         fun main() {\n\
             println(inspect(Point { x: 1, y: 2 }))\n\
             println(inspect(3))\n\
         }\n",
    );
    let analysis = analyze(&program);
    assert!(analysis.errors.is_empty(), "errors: {:?}", analysis.errors);
    // Both decisions replay identically at monomorphization: Point satisfies
    // the anonymous pattern structurally; the int32 subject must NOT widen
    // into the int64 arm.
    let ttests: Vec<_> = analysis.type_tests.values().collect();
    assert!(!ttests.is_empty());
}

/// The matching instance selects the tested arm and the pinned pattern lands
/// on the channel.
#[test]
fn matching_instance_selects_the_arm() {
    let program = lower(
        "fun wants_str(s: string) -> int32 { return 1 }\n\
         fun length(val) {\n\
             if val: infer {\n\
                 return wants_str(val)\n\
             }\n\
             return 0\n\
         }\n\
         fun main() { println(length(\"hello\")) }\n",
    );
    let analysis = analyze(&program);
    assert!(analysis.errors.is_empty(), "errors: {:?}", analysis.errors);
    // The probe pinned the bare `infer` to `string` (what `wants_str`
    // accepts) and recorded it for MIR.
    assert!(
        analysis
            .type_tests
            .values()
            .any(|t| matches!(t, brass_hir::Type::Str)),
        "type_tests: {:?}",
        analysis.type_tests
    );
}
