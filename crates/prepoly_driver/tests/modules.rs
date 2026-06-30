//! End-to-end module-resolution tests. These exercise the
//! driver's file-system module loader, which the per-crate unit tests cannot
//! reach: missing module files, private module files, and import-name checking.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

/// Create an isolated module tree under the test binary's temp dir and return
/// the path to its `main.pp`. `files` is a list of (relative path, source).
fn setup(case: &str, files: &[(&str, &str)]) -> PathBuf {
    let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(case);
    let _ = fs::remove_dir_all(&root);
    for (rel, src) in files {
        let path = root.join(rel);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, src).unwrap();
    }
    root.join("main.pp")
}

/// Run `prepoly check <main>` and return (success, combined output).
fn check(main: &PathBuf) -> (bool, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_prepoly"))
        .arg("check")
        .arg(main)
        .output()
        .expect("spawn prepoly");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    (out.status.success(), combined)
}

#[test]
fn valid_cross_module_import_succeeds() {
    let main = setup(
        "valid_import",
        &[
            ("lib/util.pp", "fun helper() -> int32 { return 7 }\n"),
            (
                "main.pp",
                "import lib.util.{ helper }\nfun main() { println(helper()) }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(ok, "expected success, got: {out}");
}

#[test]
fn import_is_relative_to_the_importing_file() {
    // `modules/a.pp` and `modules/b.pp` are siblings; `a.pp` imports `b.pp` as
    // `import b`, resolved relative to a.pp's own directory rather than the main
    // file's. (Relative to the main file, `import b` would look for `./b.pp`.)
    let main = setup(
        "relative_import",
        &[
            ("modules/b.pp", "fun b_val() -> int32 { return 42 }\n"),
            (
                "modules/a.pp",
                "import b.{ b_val }\nfun a_val() -> int32 { return b_val() }\n",
            ),
            (
                "main.pp",
                "import modules.a.{ a_val }\nfun main() { println(a_val()) }\n",
            ),
        ],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out.trim(), "42", "{out}");
}

#[test]
fn missing_module_file_is_rejected() {
    let main = setup(
        "missing_module",
        &[("main.pp", "import lib.absent.{ thing }\nfun main() { }\n")],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure");
    assert!(out.contains("cannot find module"), "{out}");
}

#[test]
fn unknown_imported_name_is_rejected() {
    let main = setup(
        "unknown_name",
        &[
            ("lib/util.pp", "fun helper() -> int32 { return 7 }\n"),
            (
                "main.pp",
                "import lib.util.{ helper, missing }\nfun main() { }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure");
    assert!(out.contains("has no exported name `missing`"), "{out}");
}

#[test]
fn error_is_attributed_to_the_correct_module_file() {
    // A type error in a non-main module reports that module's file and line.
    // Each file's spans are parsed at a disjoint base offset, so a diagnostic is
    // located in the file it came from rather than guessed by length.
    let main = setup(
        "error_attribution",
        &[
            (
                "lib/util.pp",
                "fun helper() -> int32 {\n  return \"not an int\"\n}\n",
            ),
            (
                "main.pp",
                "import lib.util.{ helper }\nfun main() { println(helper()) }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure");
    assert!(
        out.contains("lib/util.pp:2:"),
        "error should point at lib/util.pp line 2: {out}"
    );
}

#[test]
fn private_module_file_import_is_rejected() {
    let main = setup(
        "private_module",
        &[
            ("lib/_secret.pp", "fun reveal() -> int32 { return 42 }\n"),
            ("main.pp", "import lib._secret.{ reveal }\nfun main() { }\n"),
        ],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure");
    assert!(out.contains("cannot import private module"), "{out}");
}

#[test]
fn private_name_import_is_rejected() {
    let main = setup(
        "private_name",
        &[
            ("lib/util.pp", "fun _hidden() -> int32 { return 1 }\n"),
            ("main.pp", "import lib.util.{ _hidden }\nfun main() { }\n"),
        ],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure");
    assert!(out.contains("cannot import private name"), "{out}");
}

#[test]
fn non_imported_public_name_is_invisible() {
    // A public name in another module is only usable when imported; calling it
    // without an import is a name-resolution error, not a silent global lookup.
    let main = setup(
        "non_imported_public",
        &[
            (
                "lib/util.pp",
                "fun helper() -> int32 { return 1 }\nfun hidden_public() -> int32 { return 2 }\n",
            ),
            (
                "main.pp",
                "import lib.util.{ helper }\nfun main() { println(hidden_public()) }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure");
    assert!(out.contains("unknown function `hidden_public`"), "{out}");
}

#[test]
fn private_name_is_invisible_by_direct_use_from_another_module() {
    let main = setup(
        "private_direct_use",
        &[
            (
                "lib/util.pp",
                "fun helper() -> int32 { return 1 }\nfun _secret() -> int32 { return 2 }\n",
            ),
            (
                "main.pp",
                "import lib.util.{ helper }\nfun main() { println(_secret()) }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure");
    assert!(out.contains("unknown function `_secret`"), "{out}");
}

#[test]
fn same_local_name_in_different_modules_is_allowed() {
    // Two modules may both define `helper`; importing only one resolves to that
    // module's definition without a cross-module duplicate-definition error.
    let main = setup(
        "same_local_name",
        &[
            ("a/util.pp", "fun helper() -> int32 { return 1 }\n"),
            ("b/util.pp", "fun helper() -> int32 { return 2 }\n"),
            (
                "main.pp",
                "import a.util.{ helper }\nfun main() { println(helper()) }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(ok, "expected success, got: {out}");
}

#[test]
fn a_module_can_call_its_own_private_helper() {
    // A `_`-prefixed name is visible within its defining module.
    let main = setup(
        "own_private_helper",
        &[
            (
                "lib/util.pp",
                "fun _double(n: int32) -> int32 { return n * 2 }\nfun quad(n: int32) -> int32 { return _double(_double(n)) }\n",
            ),
            (
                "main.pp",
                "import lib.util.{ quad }\nfun main() { println(quad(3)) }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(ok, "expected success, got: {out}");
}

/// Run `prepoly <main>` and return (success, combined output).
fn run(main: &PathBuf) -> (bool, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_prepoly"))
        .arg(main)
        .output()
        .expect("spawn prepoly");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    (out.status.success(), combined)
}

#[test]
fn same_function_name_in_two_modules_coexists_and_dispatches() {
    // `helper` is defined in both a.util and b.util, both loaded,
    // but main imports only a.util's. main's call resolves to a.util's helper,
    // while b.util's `thing` calls b.util's own helper. Both dispatch correctly.
    let main = setup(
        "coexist_dispatch",
        &[
            ("a/util.pp", "fun helper() -> int32 { return 1 }\n"),
            (
                "b/util.pp",
                "fun helper() -> int32 { return 2 }\nfun thing() -> int32 { return helper() }\n",
            ),
            (
                "main.pp",
                "import a.util.{ helper }\nimport b.util.{ thing }\nfun main() { println(helper()) println(thing()) }\n",
            ),
        ],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert!(out.contains("1") && out.contains("2"), "{out}");
}

#[test]
fn typed_int_functions_compile_and_run_correctly() {
    // Leaf integer-arithmetic functions compile to typed unboxed
    // bodies behind uniform-ABI adapters; results must match the uniform path,
    // including truncation and sign extension across the boundary.
    let main = setup(
        "typed_int_codegen",
        &[(
            "main.pp",
            "fun add(a: int32, b: int32) -> int32 { return a + b }\n\
             fun madd(a: int32, b: int32, c: int32) -> int32 { return a * b - c }\n\
             fun neg1(x: int64) -> int64 { return -x }\n\
             fun main() { println(add(-1, 41)) println(madd(4, 5, 6)) println(neg1(9)) }\n",
        )],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert!(out.contains("40"), "add(-1,41)=40: {out}");
    assert!(out.contains("14"), "madd(4,5,6)=14: {out}");
    assert!(out.contains("-9"), "neg1(9)=-9: {out}");
}

#[test]
fn typed_integer_control_flow_runs_correctly() {
    // Typed codegen now handles integer functions with control flow
    // (if/else, locals, multiple returns), not just single-return leaf bodies.
    let main = setup(
        "typed_int_control_flow",
        &[(
            "main.pp",
            "fun maxi(a: int32, b: int32) -> int32 { if a > b { return a } return b }\n\
             fun absi(x: int32) -> int32 { if x < 0 { return -x } return x }\n\
             fun clamp(x: int32) -> int32 { let hi: int32 = 10\n if x > hi { return hi } if x < 0 { return 0 } return x }\n\
             fun main() { println(maxi(3, 7)) println(absi(-5)) println(clamp(15)) println(clamp(4)) }\n",
        )],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert!(out.contains("7"), "maxi(3,7)=7: {out}");
    assert!(out.contains("5"), "absi(-5)=5: {out}");
    assert!(out.contains("10"), "clamp(15)=10: {out}");
    assert!(out.contains("4"), "clamp(4)=4: {out}");
}

#[test]
fn typed_integer_direct_calls_run_correctly() {
    // Typed-integer functions call each other's typed instances
    // directly (no boxing round trip), resolved as a fixpoint so chains and
    // control-flow callees both qualify.
    let main = setup(
        "typed_int_calls",
        &[(
            "main.pp",
            "fun square(x: int32) -> int32 { return x * x }\n\
             fun sum_sq(a: int32, b: int32) -> int32 { return square(a) + square(b) }\n\
             fun absdiff(a: int32, b: int32) -> int32 { if a > b { return a - b } return b - a }\n\
             fun combo(a: int32, b: int32) -> int32 { let d = absdiff(a, b)\n return sum_sq(a, b) - d }\n\
             fun main() { println(sum_sq(3, 4)) println(combo(3, 4)) }\n",
        )],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert!(out.contains("25"), "sum_sq(3,4)=25: {out}");
    assert!(out.contains("24"), "combo(3,4)=24: {out}");
}

#[test]
fn typed_integer_while_loop_runs_correctly() {
    // Typed integer codegen handles while loops, compound
    // assignment, and literal-divisor division/remainder (collatz-style).
    let main = setup(
        "typed_int_while",
        &[(
            "main.pp",
            "fun collatz(n: int32) -> int32 {\n\
             let count = 0\n let x = n\n\
             while x != 1 {\n\
             if x % 2 == 0 { x = x / 2 } else { x = 3 * x + 1 }\n\
             count += 1\n }\n return count\n}\n\
             fun main() { println(collatz(6)) println(collatz(27)) }\n",
        )],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert!(out.contains("8"), "collatz(6)=8: {out}");
    assert!(out.contains("111"), "collatz(27)=111: {out}");
}

#[test]
fn typed_float_and_comparison_functions_run_correctly() {
    // The typed leaf path covers float64 arithmetic and integer/
    // float comparisons (bool-returning), through typed bodies + adapters.
    let main = setup(
        "typed_float_cmp",
        &[(
            "main.pp",
            "fun scale(x: float64, k: float64) -> float64 { return x * k + 1.0 }\n\
             fun lt(a: int32, b: int32) -> bool { return a < b }\n\
             fun feq(a: float64, b: float64) -> bool { return a == b }\n\
             fun main() { println(scale(3.0, 2.0)) println(lt(2, 5)) println(lt(5, 2)) println(feq(1.5, 1.5)) }\n",
        )],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert!(out.contains("7.0"), "scale(3,2)=7.0: {out}");
    assert!(out.contains("true"), "lt(2,5)/feq true: {out}");
    assert!(out.contains("false"), "lt(5,2) false: {out}");
}

#[test]
fn non_imported_type_in_annotation_is_rejected() {
    // A type from another module is not visible in an annotation
    // unless imported, even though it is public.
    let main = setup(
        "type_annotation_visibility",
        &[
            ("lib/m.pp", "type Secret = {\n    x: int32\n}\n"),
            (
                "main.pp",
                "import lib.m.{ }\nfun use_it(s: Secret) -> int32 { return s.x }\nfun main() { }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure");
    assert!(out.contains("unknown type `Secret`"), "{out}");
}

#[test]
fn imported_type_in_annotation_is_accepted() {
    let main = setup(
        "type_annotation_imported",
        &[
            (
                "lib/m.pp",
                "type Pt = {\n    x: int32\n}\nfun origin() -> Pt { return Pt { x: 0 } }\n",
            ),
            (
                "main.pp",
                "import lib.m.{ Pt, origin }\nfun get_x(p: Pt) -> int32 { return p.x }\nfun main() { println(get_x(origin())) }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(ok, "expected success, got: {out}");
}

#[test]
fn same_type_name_in_two_modules_constructs_and_dispatches() {
    // `Shape` is defined in both a.shape and b.shape with different
    // fields and `area` methods. Each module constructs its own Shape, and
    // method dispatch on a value resolves to that value's type's method.
    let main = setup(
        "coexist_types",
        &[
            (
                "a/shape.pp",
                "type Shape = {\n    side: float64\n    area(self) -> float64 { return self.side * self.side }\n}\nfun make_a(s: float64) -> Shape { return Shape { side: s } }\n",
            ),
            (
                "b/shape.pp",
                "type Shape = {\n    r: float64\n    area(self) -> float64 { return 3.0 * self.r }\n}\nfun make_b(r: float64) -> Shape { return Shape { r: r } }\n",
            ),
            (
                "main.pp",
                "import a.shape.{ make_a }\nimport b.shape.{ make_b }\nfun main() { println(make_a(3.0).area()) println(make_b(2.0).area()) }\n",
            ),
        ],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    // a's area: 3*3 = 9; b's area: 3*2 = 6. Each dispatched to its own type.
    assert!(out.contains("9.0") && out.contains("6.0"), "{out}");
}

#[test]
fn importing_same_name_from_two_modules_is_ambiguous() {
    // The same function name defined in two modules now coexists; the
    // error is the ambiguous import into the module that pulls in both.
    let main = setup(
        "cross_module_collision",
        &[
            ("a/util.pp", "fun helper() -> int32 { return 1 }\n"),
            ("b/util.pp", "fun helper() -> int32 { return 2 }\n"),
            (
                "main.pp",
                "import a.util.{ helper }\nimport b.util.{ helper }\nfun main() { let _ = helper() }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure");
    assert!(
        out.contains("`helper` is imported from multiple modules"),
        "{out}"
    );
}

#[test]
fn stdlib_string_function_rejects_wrong_argument_type() {
    // Annotated public stdlib signatures enforce their contracts, so
    // calling `split` with a non-string argument is a static error.
    let main = setup(
        "stdlib_string_contract",
        &[("main.pp", "fun main() { let _ = split(123, \",\") }\n")],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure");
    assert!(
        out.contains("cannot use `int32` where `string` is required"),
        "{out}"
    );
}
