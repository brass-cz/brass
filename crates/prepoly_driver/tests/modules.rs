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
    assert!(
        out.contains("`hidden_public` is defined in module `lib.util` but not imported here"),
        "{out}"
    );
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
    assert!(
        out.contains("`_secret` is private to module `lib.util`"),
        "{out}"
    );
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
fn same_global_name_in_two_modules_gets_its_own_slot() {
    // Both modules define a top-level `let tag`; global storage is keyed per
    // defining module, so `m`'s function must read `m`'s value while main reads
    // its own -- bare-name keying collapsed the two into one slot, and a
    // mutation in `m` must not touch main's `tag` either. Pinned on both back
    // ends (the JIT and the REPL interpreter share the MIR global keys).
    let main = setup(
        "global_per_module",
        &[
            (
                "m.pp",
                "let tag = \"module\"\nlet counter = 0\n\
                 fun mtag() -> string { return tag }\n\
                 fun bump() { counter = counter + 1 }\n\
                 fun count() -> int64 { return counter }\n",
            ),
            (
                "main.pp",
                "import m.{ mtag, bump, count }\n\nlet tag = \"main\"\n\
                 fun main() { println(mtag()) println(tag) bump() bump() println(count()) }\n",
            ),
        ],
    );
    let expected = "module\nmain\n2\n";
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out, expected, "JIT global slots collided");
    let out = Command::new(env!("CARGO_BIN_EXE_prepoly"))
        .arg("repl")
        .arg(&main)
        .output()
        .expect("spawn prepoly repl");
    assert!(out.status.success(), "repl run failed");
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        expected,
        "REPL global slots collided"
    );
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
                "type Shape = {\n    side: float64\n}\nfun Shape.area(self) -> float64 { return self.side * self.side }\nfun make_a(s: float64) -> Shape { return Shape { side: s } }\n",
            ),
            (
                "b/shape.pp",
                "type Shape = {\n    r: float64\n}\nfun Shape.area(self) -> float64 { return 3.0 * self.r }\nfun make_b(r: float64) -> Shape { return Shape { r: r } }\n",
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
    // Annotated public stdlib signatures enforce their contracts, so calling the
    // `string.split` method with a non-string separator is a static error.
    let main = setup(
        "stdlib_string_contract",
        &[("main.pp", "fun main() { let _ = \"a,b\".split(123) }\n")],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure");
    assert!(
        out.contains("cannot use `int32` where `string` is required"),
        "{out}"
    );
}

#[test]
fn phantom_std_import_is_rejected() {
    // An import from a module that was never loaded (`std.phantom`) used to
    // fall back to accepting any name defined anywhere in the program, which
    // made every module's definitions reachable without importing the module.
    // Only genuine std exports resolve for unloaded paths; anything else is an
    // unknown module.
    let main = setup(
        "phantom_std_import",
        &[
            ("a/util.pp", "fun secret_helper() -> int32 { return 42 }\n"),
            (
                "loader.pp",
                "import a.util.{ secret_helper }\nfun use_it() -> int32 { return secret_helper() }\n",
            ),
            (
                "main.pp",
                "import loader.{ use_it }\nimport std.phantom.{ secret_helper }\n\
                 fun main() { println(secret_helper()) }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure, got: {out}");
    assert!(
        out.contains("cannot import from unknown module `std.phantom`"),
        "{out}"
    );
}

#[test]
fn bare_prelude_import_still_resolves() {
    // The bare prelude spelling (`import conv.{ ... }`) aliases the loaded
    // `std.conv` module and keeps resolving against its real exports, while a
    // name conv does not export is rejected against those same exports.
    let main = setup(
        "bare_prelude_import",
        &[(
            "main.pp",
            "import conv.{ int32_parse }\nfun main() { println(int32_parse(\"41\")! + 1) }\n",
        )],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert!(out.contains("42"), "{out}");
    let bad = setup(
        "bare_prelude_import_bad",
        &[(
            "main.pp",
            "import conv.{ no_such_export }\nfun main() { println(1) }\n",
        )],
    );
    let (ok, out) = check(&bad);
    assert!(!ok, "expected failure, got: {out}");
    assert!(
        out.contains("module `conv` has no exported name `no_such_export`"),
        "{out}"
    );
}

/// `import a.b` (no braces, path names a module) makes the module's exports
/// usable qualified by the last path segment: functions, types in type
/// position, record literals, and static calls.
#[test]
fn module_import_allows_qualified_use() {
    let main = setup(
        "module_import_qualified",
        &[
            (
                "geometry/vec.pp",
                "type Vec2 = {\n    x: float64\n    y: float64\n}\nfun Vec2.new(x: float64, y: float64) {\n    return Self { x: x, y: y }\n}\nfun dot(a: Vec2, b: Vec2) -> float64 {\n    return a.x * b.x + a.y * b.y\n}\n",
            ),
            (
                "main.pp",
                "import geometry.vec\nfun main() {\n    let a: vec.Vec2 = vec.Vec2.new(1.0, 2.0)\n    let b = vec.Vec2 { x: 3.0, y: 4.0 }\n    println(vec.dot(a, b))\n}\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(ok, "expected success, got: {out}");
}

/// `import a.b.X` (no braces, path prefix names a module) imports the single
/// name `X`, exactly like `import a.b.{ X }`.
#[test]
fn single_name_import_is_the_braced_form() {
    let main = setup(
        "single_name_import",
        &[
            ("lib/util.pp", "fun helper() -> int32 { return 7 }\n"),
            (
                "main.pp",
                "import lib.util.helper\nfun main() { println(helper()) }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(ok, "expected success, got: {out}");
}

/// Two module imports whose paths end in the same segment cannot both be used
/// qualified; the collision is reported at the second import.
#[test]
fn duplicate_qualifier_is_rejected() {
    let main = setup(
        "duplicate_qualifier",
        &[
            ("a/util.pp", "fun f() -> int32 { return 1 }\n"),
            ("b/util.pp", "fun g() -> int32 { return 2 }\n"),
            (
                "main.pp",
                "import a.util\nimport b.util\nfun main() { println(util.f()) }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure");
    assert!(
        out.contains("two module imports share the qualifier `util`"),
        "got: {out}"
    );
}

/// A local binding shadows a module qualifier: `vec.x` after `let vec = ..`
/// is a field access, and the program still checks.
#[test]
fn local_binding_shadows_the_qualifier() {
    let main = setup(
        "qualifier_shadowed",
        &[
            ("geometry/vec.pp", "fun dot() -> int32 { return 9 }\n"),
            (
                "main.pp",
                "import geometry.vec\ntype P = { x: float64 }\nfun main() {\n    let vec = P { x: 7.5 }\n    println(vec.x)\n}\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(ok, "expected success, got: {out}");
}

/// Qualified access to a private (`_`-prefixed) name is rejected at the use.
#[test]
fn qualified_private_access_is_rejected() {
    let main = setup(
        "qualified_private",
        &[
            ("geometry/vec.pp", "fun _helper() -> int32 { return 1 }\n"),
            (
                "main.pp",
                "import geometry.vec\nfun main() {\n    println(vec._helper())\n}\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure");
    assert!(
        out.contains("cannot access private name `_helper`"),
        "got: {out}"
    );
}

/// A qualified use of a name the module does not export is reported against
/// the module's export list (the same check a braced import gets).
#[test]
fn qualified_unknown_name_is_rejected() {
    let main = setup(
        "qualified_unknown",
        &[
            ("geometry/vec.pp", "fun dot() -> int32 { return 1 }\n"),
            (
                "main.pp",
                "import geometry.vec\nfun main() {\n    println(vec.nosuch())\n}\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure");
    assert!(out.contains("no exported name `nosuch`"), "got: {out}");
}

/// `alias.Sum.Variant { .. }` constructs a variant through a module import.
#[test]
fn qualified_variant_construction() {
    let main = setup(
        "qualified_variant",
        &[
            (
                "shapes/lib.pp",
                "\
type Shape =
    | Circle { r: float64 }
    | Dot

fun describe(s: Shape) -> string {
    return match s {
        Shape.Circle { r } => \"circle {r}\",
        Shape.Dot => \"dot\",
    }
}
",
            ),
            (
                "main.pp",
                "\
import shapes.lib

fun main() {
    let c = lib.Shape.Circle { r: 2.5 }
    println(lib.describe(c))
}
",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(ok, "expected success, got: {out}");
}

/// Qualified variant construction produces correct output at runtime.
#[test]
fn qualified_variant_construction_runs() {
    let main = setup(
        "qualified_variant_run",
        &[
            (
                "shapes/lib.pp",
                "\
type Shape =
    | Circle { r: float64 }
    | Dot

fun describe(s: Shape) -> string {
    return match s {
        Shape.Circle { r } => \"circle {r}\",
        Shape.Dot => \"dot\",
    }
}
",
            ),
            (
                "main.pp",
                "\
import shapes.lib

fun main() {
    let c = lib.Shape.Circle { r: 2.5 }
    println(lib.describe(c))
    println(lib.describe(lib.Shape.Dot))
}
",
            ),
        ],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out.trim(), "circle 2.5\ndot");
}

/// A shadowed qualifier prevents the qualified variant rewrite: `let lib = ..`
/// then `lib.Shape.Circle { .. }` is a field chain, not a qualified variant.
#[test]
fn shadowed_qualifier_blocks_qualified_variant() {
    let main = setup(
        "qualified_variant_shadowed",
        &[
            (
                "shapes/lib.pp",
                "\
type Shape =
    | Circle { r: float64 }
    | Dot
",
            ),
            (
                "main.pp",
                "\
import shapes.lib
type P = { Shape: int32 }
fun main() {
    let lib = P { Shape: 1 }
    println(lib.Shape)
}
",
            ),
        ],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out.trim(), "1");
}

/// `import a.util as au` renames the qualifier, resolving a duplicate.
#[test]
fn module_import_as_resolves_duplicate_qualifier() {
    let main = setup(
        "module_import_as",
        &[
            ("a/util.pp", "fun f() -> int32 { return 1 }\n"),
            ("b/util.pp", "fun g() -> int32 { return 2 }\n"),
            (
                "main.pp",
                "\
import a.util as au
import b.util as bu

fun main() {
    println(au.f())
    println(bu.g())
}
",
            ),
        ],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out.trim(), "1\n2");
}

/// `import ... as` with the original last segment reused as a qualifier
/// still works (no-op rename).
#[test]
fn module_import_as_same_name() {
    let main = setup(
        "module_import_as_same",
        &[
            ("geometry/vec.pp", "fun dot() -> int32 { return 42 }\n"),
            (
                "main.pp",
                "\
import geometry.vec as vec

fun main() {
    println(vec.dot())
}
",
            ),
        ],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out.trim(), "42");
}

/// `import a.b.{ X as Y }` renames a single imported name: `Y` is in scope,
/// `X` is not. The remote name resolves correctly in the target module.
#[test]
fn name_import_as_renames_in_scope() {
    let main = setup(
        "name_import_as",
        &[
            ("lib/util.pp", "fun helper() -> int32 { return 42 }\n"),
            (
                "main.pp",
                "\
import lib.util.{ helper as h }

fun main() {
    println(h())
}
",
            ),
        ],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out.trim(), "42");
}

/// The original remote name is NOT in scope after a rename.
#[test]
fn name_import_as_hides_remote_name() {
    let main = setup(
        "name_import_as_hide",
        &[
            ("lib/util.pp", "fun helper() -> int32 { return 42 }\n"),
            (
                "main.pp",
                "\
import lib.util.{ helper as h }

fun main() {
    println(helper())
}
",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure, got: {out}");
}

/// `import a.b.X as Y` (bare single-name form with rename).
#[test]
fn bare_single_name_import_as() {
    let main = setup(
        "bare_single_name_as",
        &[
            ("lib/util.pp", "fun helper() -> int32 { return 99 }\n"),
            (
                "main.pp",
                "\
import lib.util.helper as h

fun main() {
    println(h())
}
",
            ),
        ],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out.trim(), "99");
}

/// Two renamed imports that collide on their LOCAL name are ambiguous.
#[test]
fn renamed_local_collision_is_ambiguous() {
    let main = setup(
        "renamed_local_collision",
        &[
            ("a/util.pp", "fun f() -> int32 { return 1 }\n"),
            ("b/util.pp", "fun g() -> int32 { return 2 }\n"),
            (
                "main.pp",
                "\
import a.util.{ f as h }
import b.util.{ g as h }

fun main() {
    println(h())
}
",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure");
    assert!(
        out.contains("is imported from multiple modules"),
        "got: {out}"
    );
}

// ===== PREPOLY_INCLUDE / PREPOLY_PACKAGES resolution =====

/// Create a bare file tree (no `main.pp` convention) under the test binary's
/// temp dir and return its root, for use as a `PREPOLY_INCLUDE` entry or a
/// `PREPOLY_PACKAGES` directory.
fn setup_tree(case: &str, files: &[(&str, &str)]) -> PathBuf {
    let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(case);
    let _ = fs::remove_dir_all(&root);
    for (rel, src) in files {
        let path = root.join(rel);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, src).unwrap();
    }
    root
}

/// Run `prepoly [check] <main>` with the given environment variables set and
/// return (success, combined output).
fn with_env(main: &PathBuf, envs: &[(&str, &str)], mode: &str) -> (bool, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_prepoly"));
    if mode == "check" {
        cmd.arg("check");
    }
    cmd.arg(main);
    for (key, val) in envs {
        cmd.env(key, val);
    }
    let out = cmd.output().expect("spawn prepoly");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    (out.status.success(), combined)
}

/// Run `prepoly [check] <main>` with `PREPOLY_INCLUDE` set to `include`.
fn with_include(main: &PathBuf, include: &str, mode: &str) -> (bool, String) {
    with_env(main, &[("PREPOLY_INCLUDE", include)], mode)
}

#[test]
fn include_module_resolves_braced_and_qualified() {
    // A module under an include path imports exactly like a local file: with
    // a brace list and as a bare module import used qualified.
    let inc = setup_tree(
        "inc_basic_lib",
        &[("mylib.pp", "fun seven() -> int32 { return 7 }\n")],
    );
    let main = setup(
        "inc_basic",
        &[(
            "main.pp",
            "import mylib.{ seven }\nfun main() { println(seven()) }\n",
        )],
    );
    let (ok, out) = with_include(&main, &inc.display().to_string(), "check");
    assert!(ok, "expected success, got: {out}");
    let main = setup(
        "inc_basic_qualified",
        &[(
            "main.pp",
            "import mylib\nfun main() { println(mylib.seven()) }\n",
        )],
    );
    let (ok, out) = with_include(&main, &inc.display().to_string(), "check");
    assert!(ok, "expected success, got: {out}");
}

#[test]
fn include_submodule_and_sibling_imports_resolve() {
    // A library under an include path uses the same layout as a local tree:
    // the root file imports its own submodule, and submodules import their
    // siblings relative to their own directory.
    let inc = setup_tree(
        "inc_lib_tree_lib",
        &[
            (
                "mylib.pp",
                "import mylib.a.{ a_val }\nfun api() -> int32 { return a_val() }\n",
            ),
            (
                "mylib/a.pp",
                "import b.{ b_val }\nfun a_val() -> int32 { return b_val() }\n",
            ),
            ("mylib/b.pp", "fun b_val() -> int32 { return 41 }\n"),
        ],
    );
    let main = setup(
        "inc_lib_tree",
        &[(
            "main.pp",
            "import mylib.{ api }\nimport mylib.b.{ b_val }\nfun main() { println(api() + 1) println(b_val()) }\n",
        )],
    );
    let (ok, out) = with_include(&main, &inc.display().to_string(), "");
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out.trim(), "42\n41", "{out}");
}

#[test]
fn project_file_shadows_include_module() {
    // The project root is searched before the include paths, so a local file
    // with the same module path wins over the include one.
    let inc = setup_tree(
        "inc_shadow_lib",
        &[("dup.pp", "fun which() -> string { return \"include\" }\n")],
    );
    let main = setup(
        "inc_shadow",
        &[
            ("dup.pp", "fun which() -> string { return \"project\" }\n"),
            (
                "main.pp",
                "import dup.{ which }\nfun main() { println(which()) }\n",
            ),
        ],
    );
    let (ok, out) = with_include(&main, &inc.display().to_string(), "");
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out.trim(), "project", "{out}");
}

#[test]
fn earlier_include_entry_wins() {
    // Include paths are searched in list order; the first entry serving the
    // path shadows later ones.
    let first = setup_tree(
        "inc_order_first",
        &[("pick.pp", "fun which() -> string { return \"first\" }\n")],
    );
    let second = setup_tree(
        "inc_order_second",
        &[("pick.pp", "fun which() -> string { return \"second\" }\n")],
    );
    let main = setup(
        "inc_order",
        &[(
            "main.pp",
            "import pick.{ which }\nfun main() { println(which()) }\n",
        )],
    );
    let joined = format!("{}:{}", first.display(), second.display());
    let (ok, out) = with_include(&main, &joined, "");
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out.trim(), "first", "{out}");
    let joined = format!("{}:{}", second.display(), first.display());
    let (ok, out) = with_include(&main, &joined, "");
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out.trim(), "second", "{out}");
}

#[test]
fn nested_project_module_reaches_include_library() {
    // An import written in a nested module resolves relative to that module
    // first; when nothing serves the relative form, the path as written is
    // looked up under the include paths.
    let inc = setup_tree(
        "inc_from_nested_lib",
        &[("mylib.pp", "fun seven() -> int32 { return 7 }\n")],
    );
    let main = setup(
        "inc_from_nested",
        &[
            (
                "modules/a.pp",
                "import mylib.{ seven }\nfun f() -> int32 { return seven() }\n",
            ),
            (
                "main.pp",
                "import modules.a.{ f }\nfun main() { println(f()) }\n",
            ),
        ],
    );
    let (ok, out) = with_include(&main, &inc.display().to_string(), "check");
    assert!(ok, "expected success, got: {out}");
}

#[test]
fn missing_module_error_mentions_include_search() {
    // With include paths set, the missing-module error says they were
    // searched, so the user knows the lookup went beyond the project root.
    let inc = setup_tree(
        "inc_missing_lib",
        &[("other.pp", "fun x() -> int32 { return 1 }\n")],
    );
    let main = setup(
        "inc_missing",
        &[("main.pp", "import nosuch.{ y }\nfun main() { }\n")],
    );
    let (ok, out) = with_include(&main, &inc.display().to_string(), "check");
    assert!(!ok, "expected failure");
    assert!(out.contains("cannot find module `nosuch`"), "{out}");
    assert!(out.contains("include path"), "{out}");
}

#[test]
fn empty_include_entries_are_skipped() {
    // Leading, trailing, and doubled colons contribute no include entries and
    // do not break resolution of what remains.
    let inc = setup_tree(
        "inc_empty_entries_lib",
        &[("mylib.pp", "fun seven() -> int32 { return 7 }\n")],
    );
    let main = setup(
        "inc_empty_entries",
        &[(
            "main.pp",
            "import mylib.{ seven }\nfun main() { println(seven()) }\n",
        )],
    );
    let val = format!("::{}:", inc.display());
    let (ok, out) = with_include(&main, &val, "check");
    assert!(ok, "expected success, got: {out}");
    // An entirely empty variable is the same as an unset one.
    let main = setup(
        "inc_empty_var",
        &[
            ("lib/util.pp", "fun helper() -> int32 { return 7 }\n"),
            (
                "main.pp",
                "import lib.util.{ helper }\nfun main() { println(helper()) }\n",
            ),
        ],
    );
    let (ok, out) = with_include(&main, "", "check");
    assert!(ok, "expected success, got: {out}");
}

/// `import c.{ X }` + `import a.b` + both `X` and `b.X` used — green, each
/// resolving to its own definition (bare `X` is c's, `b.X` is a.b's).
#[test]
fn qualified_use_disambiguates_from_braced_import() {
    let main = setup(
        "qualified_disambiguates",
        &[
            ("c.pp", "fun X() -> int32 { return 1 }\n"),
            ("a/b.pp", "fun X() -> int32 { return 2 }\n"),
            (
                "main.pp",
                "\
import c.{ X }
import a.b

fun main() {
    println(X())
    println(b.X())
}
",
            ),
        ],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out.trim(), "1\n2");
}

#[test]
fn packages_env_scopes_resolution_to_the_declared_name() {
    // A `PREPOLY_PACKAGES` entry serves imports rooted at its declared name
    // -- and ONLY those: a second module in the same directory is not
    // importable, unlike an open include path.
    let pkg = setup_tree(
        "pkg_scoped_dir",
        &[
            ("mylib.pp", "fun seven() -> int32 { return 7 }\n"),
            ("other.pp", "fun eight() -> int32 { return 8 }\n"),
        ],
    );
    let packages = format!("mylib={}", pkg.display());
    let main = setup(
        "pkg_scoped",
        &[(
            "main.pp",
            "import mylib.{ seven }\nfun main() { println(seven()) }\n",
        )],
    );
    let (ok, out) = with_env(&main, &[("PREPOLY_PACKAGES", &packages)], "check");
    assert!(ok, "expected success, got: {out}");
    let main = setup(
        "pkg_scoped_other",
        &[(
            "main.pp",
            "import other.{ eight }\nfun main() { println(eight()) }\n",
        )],
    );
    let (ok, out) = with_env(&main, &[("PREPOLY_PACKAGES", &packages)], "check");
    assert!(!ok, "undeclared module must not resolve, got: {out}");
    assert!(out.contains("cannot find module `other`"), "{out}");
}

#[test]
fn package_name_binds_before_a_project_file() {
    // A declared package name owns its import namespace: it wins over a
    // same-named file in the project (the opposite of the include rule, where
    // the project shadows the include).
    let pkg = setup_tree(
        "pkg_binds_dir",
        &[("dup.pp", "fun which() -> string { return \"package\" }\n")],
    );
    let packages = format!("dup={}", pkg.display());
    let main = setup(
        "pkg_binds",
        &[
            ("dup.pp", "fun which() -> string { return \"project\" }\n"),
            (
                "main.pp",
                "import dup.{ which }\nfun main() { println(which()) }\n",
            ),
        ],
    );
    let (ok, out) = with_env(&main, &[("PREPOLY_PACKAGES", &packages)], "");
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out.trim(), "package", "{out}");
}

#[test]
fn packages_and_include_coexist() {
    // Both variables set at once: the package map serves its declared name,
    // the include path serves everything else.
    let pkg = setup_tree(
        "pkg_coexist_pkg",
        &[("mylib.pp", "fun seven() -> int32 { return 7 }\n")],
    );
    let inc = setup_tree(
        "pkg_coexist_inc",
        &[("openlib.pp", "fun eight() -> int32 { return 8 }\n")],
    );
    let packages = format!("mylib={}", pkg.display());
    let include = inc.display().to_string();
    let main = setup(
        "pkg_coexist",
        &[(
            "main.pp",
            "import mylib.{ seven }\nimport openlib.{ eight }\nfun main() { println(seven() + eight()) }\n",
        )],
    );
    let envs = [
        ("PREPOLY_PACKAGES", packages.as_str()),
        ("PREPOLY_INCLUDE", include.as_str()),
    ];
    let (ok, out) = with_env(&main, &envs, "");
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out.trim(), "15", "{out}");
}

#[test]
fn declared_package_missing_module_does_not_fall_through() {
    // A declared name whose directory lacks the module is an error even when
    // an include path could serve the same path: the declaration owns it.
    let pkg = setup_tree("pkg_owns_dir", &[("unrelated.txt", "")]);
    let inc = setup_tree(
        "pkg_owns_inc",
        &[("mylib.pp", "fun seven() -> int32 { return 7 }\n")],
    );
    let packages = format!("mylib={}", pkg.display());
    let include = inc.display().to_string();
    let main = setup(
        "pkg_owns",
        &[(
            "main.pp",
            "import mylib.{ seven }\nfun main() { println(seven()) }\n",
        )],
    );
    let envs = [
        ("PREPOLY_PACKAGES", packages.as_str()),
        ("PREPOLY_INCLUDE", include.as_str()),
    ];
    let (ok, out) = with_env(&main, &envs, "check");
    assert!(!ok, "expected failure, got: {out}");
    assert!(out.contains("cannot find module `mylib`"), "{out}");
}

#[test]
fn distributed_binary_includes_its_sibling_libraries_dir() {
    // A toolchain laid out as `bin/prepoly` + `libraries/` makes the shipped
    // libraries importable with no environment setup: the binary's own
    // location implies `../libraries` as a trailing include path.
    let dist = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("dist_layout");
    let _ = fs::remove_dir_all(&dist);
    fs::create_dir_all(dist.join("bin")).unwrap();
    fs::create_dir_all(dist.join("libraries")).unwrap();
    let bin = dist.join("bin/prepoly");
    fs::copy(env!("CARGO_BIN_EXE_prepoly"), &bin).unwrap();
    fs::write(
        dist.join("libraries/shipped.pp"),
        "fun greet() -> string { return \"shipped\" }\n",
    )
    .unwrap();
    let main = setup(
        "dist_layout_case",
        &[(
            "main.pp",
            "import shipped.{ greet }\nfun main() { println(greet()) }\n",
        )],
    );
    let out = Command::new(&bin)
        .arg(&main)
        .output()
        .expect("spawn dist prepoly");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "expected success, got: {stdout}{stderr}"
    );
    assert_eq!(stdout.trim(), "shipped", "{stdout}");
    // An explicit include path is searched before the implicit one.
    let inc = setup_tree(
        "dist_layout_inc",
        &[(
            "shipped.pp",
            "fun greet() -> string { return \"explicit\" }\n",
        )],
    );
    let out = Command::new(&bin)
        .arg(&main)
        .env("PREPOLY_INCLUDE", &inc)
        .output()
        .expect("spawn dist prepoly");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert_eq!(stdout.trim(), "explicit", "{stdout}");
}

/// A module's top-level bindings are exported like its functions and types, in
/// every form an import takes: by name, renamed, and through a module qualifier.
/// Only functions and types used to be collected as exports, so importing a
/// `const` was rejected as a name the module did not have.
#[test]
fn top_level_bindings_are_importable() {
    let main = setup(
        "import_globals",
        &[
            (
                "lib/consts.pp",
                "const VERSION = \"1.0.0\"\nconst MAX: int32 = 10\nconst LIMITS: int32[] = [1, 2]\nconst _SECRET = \"hidden\"\n",
            ),
            (
                "main.pp",
                "import lib.consts.{ VERSION, MAX as CAP }\n\
                 import lib.consts as C\n\
                 fun main() {\n\
                 \x20   println(VERSION)\n\
                 \x20   println(CAP)\n\
                 \x20   println(C.LIMITS)\n\
                 }\n",
            ),
        ],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out, "1.0.0\n10\n[1, 2]\n", "{out}");
}

/// A private top-level binding is not exported, like any other private name.
#[test]
fn a_private_top_level_binding_is_not_importable() {
    let main = setup(
        "import_private_global",
        &[
            ("lib/consts.pp", "const _SECRET = \"hidden\"\n"),
            (
                "main.pp",
                "import lib.consts.{ _SECRET }\nfun main() { println(_SECRET) }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "a private binding must not import: {out}");
    assert!(
        out.contains("cannot import private name `_SECRET`"),
        "{out}"
    );
}

/// Globals are keyed per DEFINING module, so two modules' same-named `const`s are
/// two globals with two types. A name-keyed table handed one module the other's
/// type -- and the back end then read the wrong slot at it.
#[test]
fn same_global_name_in_two_modules_keeps_its_own_type() {
    let main = setup(
        "same_global_name",
        &[
            (
                "lib/a.pp",
                "const MAX: int32 = 7\nfun a_max() -> int32 { return MAX }\n",
            ),
            (
                "lib/b.pp",
                "const MAX = \"seven\"\nfun b_max() -> string { return MAX }\n",
            ),
            (
                "main.pp",
                "import lib.a.{ a_max }\n\
                 import lib.b.{ b_max }\n\
                 fun main() {\n\
                 \x20   println(a_max())\n\
                 \x20   println(b_max())\n\
                 }\n",
            ),
        ],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out, "7\nseven\n", "{out}");
}
