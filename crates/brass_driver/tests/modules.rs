//! End-to-end module-resolution tests. These exercise the
//! driver's file-system module loader, which the per-crate unit tests cannot
//! reach: missing module files, private module files, and import-name checking.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

/// Create an isolated module tree under the test binary's temp dir and return
/// the path to its `main.cz`. `files` is a list of (relative path, source).
fn setup(case: &str, files: &[(&str, &str)]) -> PathBuf {
    let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(case);
    let _ = fs::remove_dir_all(&root);
    for (rel, src) in files {
        let path = root.join(rel);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, src).unwrap();
    }
    root.join("main.cz")
}

/// Run `brass check <main>` and return (success, combined output).
fn check(main: &PathBuf) -> (bool, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_brass"))
        .env("BRASS_CACHE", "off")
        .arg("check")
        .arg(main)
        .output()
        .expect("spawn brass");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    (out.status.success(), combined)
}

#[test]
fn valid_cross_module_import_succeeds() {
    let main = setup(
        "valid_import",
        &[
            ("lib/util.cz", "fun helper() -> int32 { return 7 }\n"),
            (
                "main.cz",
                "import lib.util.{ helper }\nfun main() { println(helper()) }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(ok, "expected success, got: {out}");
}

#[test]
fn import_is_relative_to_the_importing_file() {
    // `modules/a.cz` and `modules/b.cz` are siblings; `a.cz` imports `b.cz` as
    // `import b`, resolved relative to a.cz's own directory rather than the main
    // file's. (Relative to the main file, `import b` would look for `./b.cz`.)
    let main = setup(
        "relative_import",
        &[
            ("modules/b.cz", "fun b_val() -> int32 { return 42 }\n"),
            (
                "modules/a.cz",
                "import b.{ b_val }\nfun a_val() -> int32 { return b_val() }\n",
            ),
            (
                "main.cz",
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
        &[("main.cz", "import lib.absent.{ thing }\nfun main() { }\n")],
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
            ("lib/util.cz", "fun helper() -> int32 { return 7 }\n"),
            (
                "main.cz",
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
                "lib/util.cz",
                "fun helper() -> int32 {\n  return \"not an int\"\n}\n",
            ),
            (
                "main.cz",
                "import lib.util.{ helper }\nfun main() { println(helper()) }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure");
    assert!(
        out.contains("lib/util.cz:2:"),
        "error should point at lib/util.cz line 2: {out}"
    );
}

#[test]
fn private_module_file_import_is_rejected() {
    let main = setup(
        "private_module",
        &[
            ("lib/_secret.cz", "fun reveal() -> int32 { return 42 }\n"),
            ("main.cz", "import lib._secret.{ reveal }\nfun main() { }\n"),
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
            ("lib/util.cz", "fun _hidden() -> int32 { return 1 }\n"),
            ("main.cz", "import lib.util.{ _hidden }\nfun main() { }\n"),
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
                "lib/util.cz",
                "fun helper() -> int32 { return 1 }\nfun hidden_public() -> int32 { return 2 }\n",
            ),
            (
                "main.cz",
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
                "lib/util.cz",
                "fun helper() -> int32 { return 1 }\nfun _secret() -> int32 { return 2 }\n",
            ),
            (
                "main.cz",
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
            ("a/util.cz", "fun helper() -> int32 { return 1 }\n"),
            ("b/util.cz", "fun helper() -> int32 { return 2 }\n"),
            (
                "main.cz",
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
                "lib/util.cz",
                "fun _double(n: int32) -> int32 { return n * 2 }\nfun quad(n: int32) -> int32 { return _double(_double(n)) }\n",
            ),
            (
                "main.cz",
                "import lib.util.{ quad }\nfun main() { println(quad(3)) }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(ok, "expected success, got: {out}");
}

/// Run `brass <main>` and return (success, combined output).
fn run(main: &PathBuf) -> (bool, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_brass"))
        .env("BRASS_CACHE", "off")
        .arg(main)
        .output()
        .expect("spawn brass");
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
            ("a/util.cz", "fun helper() -> int32 { return 1 }\n"),
            (
                "b/util.cz",
                "fun helper() -> int32 { return 2 }\nfun thing() -> int32 { return helper() }\n",
            ),
            (
                "main.cz",
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
                "m.cz",
                "let tag = \"module\"\nlet counter = 0\n\
                 fun mtag() -> string { return tag }\n\
                 fun bump() { counter = counter + 1 }\n\
                 fun count() -> int64 { return counter }\n",
            ),
            (
                "main.cz",
                "import m.{ mtag, bump, count }\n\nlet tag = \"main\"\n\
                 fun main() { println(mtag()) println(tag) bump() bump() println(count()) }\n",
            ),
        ],
    );
    let expected = "module\nmain\n2\n";
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out, expected, "JIT global slots collided");
    let out = Command::new(env!("CARGO_BIN_EXE_brass"))
        .env("BRASS_CACHE", "off")
        .arg("repl")
        .arg(&main)
        .output()
        .expect("spawn brass repl");
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
            "main.cz",
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
            "main.cz",
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
            "main.cz",
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
            "main.cz",
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
            "main.cz",
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
            ("lib/m.cz", "type Secret = {\n    x: int32\n}\n"),
            (
                "main.cz",
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
                "lib/m.cz",
                "type Pt = {\n    x: int32\n}\nfun origin() -> Pt { return Pt { x: 0 } }\n",
            ),
            (
                "main.cz",
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
                "a/shape.cz",
                "type Shape = {\n    side: float64\n}\nfun Shape.area(self) -> float64 { return self.side * self.side }\nfun make_a(s: float64) -> Shape { return Shape { side: s } }\n",
            ),
            (
                "b/shape.cz",
                "type Shape = {\n    r: float64\n}\nfun Shape.area(self) -> float64 { return 3.0 * self.r }\nfun make_b(r: float64) -> Shape { return Shape { r: r } }\n",
            ),
            (
                "main.cz",
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
            ("a/util.cz", "fun helper() -> int32 { return 1 }\n"),
            ("b/util.cz", "fun helper() -> int32 { return 2 }\n"),
            (
                "main.cz",
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
        &[("main.cz", "fun main() { let _ = \"a,b\".split(123) }\n")],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure");
    assert!(
        out.contains("cannot use `int32` where `string` is required"),
        "{out}"
    );
}

#[test]
fn phantom_core_import_is_rejected() {
    // An import from a module that was never loaded (`core.phantom`) used to
    // fall back to accepting any name defined anywhere in the program, which
    // made every module's definitions reachable without importing the module.
    // Only genuine core exports resolve for unloaded paths; anything else is an
    // unknown module.
    let main = setup(
        "phantom_core_import",
        &[
            ("a/util.cz", "fun secret_helper() -> int32 { return 42 }\n"),
            (
                "loader.cz",
                "import a.util.{ secret_helper }\nfun use_it() -> int32 { return secret_helper() }\n",
            ),
            (
                "main.cz",
                "import loader.{ use_it }\nimport core.phantom.{ secret_helper }\n\
                 fun main() { println(secret_helper()) }\n",
            ),
        ],
    );
    let (ok, out) = check(&main);
    assert!(!ok, "expected failure, got: {out}");
    assert!(
        out.contains("cannot import from unknown module `core.phantom`"),
        "{out}"
    );
}

#[test]
fn bare_prelude_import_still_resolves() {
    // The bare prelude spelling (`import conv.{ ... }`) aliases the loaded
    // `core.conv` module and keeps resolving against its real exports, while a
    // name conv does not export is rejected against those same exports.
    let main = setup(
        "bare_prelude_import",
        &[(
            "main.cz",
            "import conv.{ int32_parse }\nfun main() { println(int32_parse(\"41\")! + 1) }\n",
        )],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert!(out.contains("42"), "{out}");
    let bad = setup(
        "bare_prelude_import_bad",
        &[(
            "main.cz",
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
                "geometry/vec.cz",
                "type Vec2 = {\n    x: float64\n    y: float64\n}\nfun Vec2.new(x: float64, y: float64) {\n    return Self { x: x, y: y }\n}\nfun dot(a: Vec2, b: Vec2) -> float64 {\n    return a.x * b.x + a.y * b.y\n}\n",
            ),
            (
                "main.cz",
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
            ("lib/util.cz", "fun helper() -> int32 { return 7 }\n"),
            (
                "main.cz",
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
            ("a/util.cz", "fun f() -> int32 { return 1 }\n"),
            ("b/util.cz", "fun g() -> int32 { return 2 }\n"),
            (
                "main.cz",
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
            ("geometry/vec.cz", "fun dot() -> int32 { return 9 }\n"),
            (
                "main.cz",
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
            ("geometry/vec.cz", "fun _helper() -> int32 { return 1 }\n"),
            (
                "main.cz",
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
            ("geometry/vec.cz", "fun dot() -> int32 { return 1 }\n"),
            (
                "main.cz",
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
                "shapes/lib.cz",
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
                "main.cz",
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
                "shapes/lib.cz",
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
                "main.cz",
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
                "shapes/lib.cz",
                "\
type Shape =
    | Circle { r: float64 }
    | Dot
",
            ),
            (
                "main.cz",
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
            ("a/util.cz", "fun f() -> int32 { return 1 }\n"),
            ("b/util.cz", "fun g() -> int32 { return 2 }\n"),
            (
                "main.cz",
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
            ("geometry/vec.cz", "fun dot() -> int32 { return 42 }\n"),
            (
                "main.cz",
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
            ("lib/util.cz", "fun helper() -> int32 { return 42 }\n"),
            (
                "main.cz",
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
            ("lib/util.cz", "fun helper() -> int32 { return 42 }\n"),
            (
                "main.cz",
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
            ("lib/util.cz", "fun helper() -> int32 { return 99 }\n"),
            (
                "main.cz",
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
            ("a/util.cz", "fun f() -> int32 { return 1 }\n"),
            ("b/util.cz", "fun g() -> int32 { return 2 }\n"),
            (
                "main.cz",
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

// ===== BRASS_INCLUDE / BRASS_PACKAGES resolution =====

/// Create a bare file tree (no `main.cz` convention) under the test binary's
/// temp dir and return its root, for use as a `BRASS_INCLUDE` entry or a
/// `BRASS_PACKAGES` directory.
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

/// Run `brass [check] <main>` with the given environment variables set and
/// return (success, combined output).
fn with_env(main: &PathBuf, envs: &[(&str, &str)], mode: &str) -> (bool, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_brass"));
    cmd.env("BRASS_CACHE", "off");
    if mode == "check" {
        cmd.arg("check");
    }
    cmd.arg(main);
    for (key, val) in envs {
        cmd.env(key, val);
    }
    let out = cmd.output().expect("spawn brass");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    (out.status.success(), combined)
}

/// Run `brass [check] <main>` with `BRASS_INCLUDE` set to `include`.
fn with_include(main: &PathBuf, include: &str, mode: &str) -> (bool, String) {
    with_env(main, &[("BRASS_INCLUDE", include)], mode)
}

#[test]
fn include_module_resolves_braced_and_qualified() {
    // A module under an include path imports exactly like a local file: with
    // a brace list and as a bare module import used qualified.
    let inc = setup_tree(
        "inc_basic_lib",
        &[("mylib.cz", "fun seven() -> int32 { return 7 }\n")],
    );
    let main = setup(
        "inc_basic",
        &[(
            "main.cz",
            "import mylib.{ seven }\nfun main() { println(seven()) }\n",
        )],
    );
    let (ok, out) = with_include(&main, &inc.display().to_string(), "check");
    assert!(ok, "expected success, got: {out}");
    let main = setup(
        "inc_basic_qualified",
        &[(
            "main.cz",
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
                "mylib.cz",
                "import mylib.a.{ a_val }\nfun api() -> int32 { return a_val() }\n",
            ),
            (
                "mylib/a.cz",
                "import b.{ b_val }\nfun a_val() -> int32 { return b_val() }\n",
            ),
            ("mylib/b.cz", "fun b_val() -> int32 { return 41 }\n"),
        ],
    );
    let main = setup(
        "inc_lib_tree",
        &[(
            "main.cz",
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
        &[("dup.cz", "fun which() -> string { return \"include\" }\n")],
    );
    let main = setup(
        "inc_shadow",
        &[
            ("dup.cz", "fun which() -> string { return \"project\" }\n"),
            (
                "main.cz",
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
        &[("pick.cz", "fun which() -> string { return \"first\" }\n")],
    );
    let second = setup_tree(
        "inc_order_second",
        &[("pick.cz", "fun which() -> string { return \"second\" }\n")],
    );
    let main = setup(
        "inc_order",
        &[(
            "main.cz",
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
        &[("mylib.cz", "fun seven() -> int32 { return 7 }\n")],
    );
    let main = setup(
        "inc_from_nested",
        &[
            (
                "modules/a.cz",
                "import mylib.{ seven }\nfun f() -> int32 { return seven() }\n",
            ),
            (
                "main.cz",
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
        &[("other.cz", "fun x() -> int32 { return 1 }\n")],
    );
    let main = setup(
        "inc_missing",
        &[("main.cz", "import nosuch.{ y }\nfun main() { }\n")],
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
        &[("mylib.cz", "fun seven() -> int32 { return 7 }\n")],
    );
    let main = setup(
        "inc_empty_entries",
        &[(
            "main.cz",
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
            ("lib/util.cz", "fun helper() -> int32 { return 7 }\n"),
            (
                "main.cz",
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
            ("c.cz", "fun X() -> int32 { return 1 }\n"),
            ("a/b.cz", "fun X() -> int32 { return 2 }\n"),
            (
                "main.cz",
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
    // A `BRASS_PACKAGES` entry serves imports rooted at its declared name
    // -- and ONLY those: a second module in the same directory is not
    // importable, unlike an open include path.
    let pkg = setup_tree(
        "pkg_scoped_dir",
        &[
            ("mylib.cz", "fun seven() -> int32 { return 7 }\n"),
            ("other.cz", "fun eight() -> int32 { return 8 }\n"),
        ],
    );
    let packages = format!("mylib={}", pkg.display());
    let main = setup(
        "pkg_scoped",
        &[(
            "main.cz",
            "import mylib.{ seven }\nfun main() { println(seven()) }\n",
        )],
    );
    let (ok, out) = with_env(&main, &[("BRASS_PACKAGES", &packages)], "check");
    assert!(ok, "expected success, got: {out}");
    let main = setup(
        "pkg_scoped_other",
        &[(
            "main.cz",
            "import other.{ eight }\nfun main() { println(eight()) }\n",
        )],
    );
    let (ok, out) = with_env(&main, &[("BRASS_PACKAGES", &packages)], "check");
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
        &[("dup.cz", "fun which() -> string { return \"package\" }\n")],
    );
    let packages = format!("dup={}", pkg.display());
    let main = setup(
        "pkg_binds",
        &[
            ("dup.cz", "fun which() -> string { return \"project\" }\n"),
            (
                "main.cz",
                "import dup.{ which }\nfun main() { println(which()) }\n",
            ),
        ],
    );
    let (ok, out) = with_env(&main, &[("BRASS_PACKAGES", &packages)], "");
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out.trim(), "package", "{out}");
}

#[test]
fn packages_and_include_coexist() {
    // Both variables set at once: the package map serves its declared name,
    // the include path serves everything else.
    let pkg = setup_tree(
        "pkg_coexist_pkg",
        &[("mylib.cz", "fun seven() -> int32 { return 7 }\n")],
    );
    let inc = setup_tree(
        "pkg_coexist_inc",
        &[("openlib.cz", "fun eight() -> int32 { return 8 }\n")],
    );
    let packages = format!("mylib={}", pkg.display());
    let include = inc.display().to_string();
    let main = setup(
        "pkg_coexist",
        &[(
            "main.cz",
            "import mylib.{ seven }\nimport openlib.{ eight }\nfun main() { println(seven() + eight()) }\n",
        )],
    );
    let envs = [
        ("BRASS_PACKAGES", packages.as_str()),
        ("BRASS_INCLUDE", include.as_str()),
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
        &[("mylib.cz", "fun seven() -> int32 { return 7 }\n")],
    );
    let packages = format!("mylib={}", pkg.display());
    let include = inc.display().to_string();
    let main = setup(
        "pkg_owns",
        &[(
            "main.cz",
            "import mylib.{ seven }\nfun main() { println(seven()) }\n",
        )],
    );
    let envs = [
        ("BRASS_PACKAGES", packages.as_str()),
        ("BRASS_INCLUDE", include.as_str()),
    ];
    let (ok, out) = with_env(&main, &envs, "check");
    assert!(!ok, "expected failure, got: {out}");
    assert!(out.contains("cannot find module `mylib`"), "{out}");
}

#[test]
fn distributed_binary_binds_its_sibling_std_dir() {
    // A toolchain laid out as `bin/brass` + `std/` makes the shipped standard
    // library importable with no environment setup: the binary's own location
    // implies its parent directory as the implicit `std` package root.
    let dist = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("dist_layout");
    let _ = fs::remove_dir_all(&dist);
    fs::create_dir_all(dist.join("bin")).unwrap();
    fs::create_dir_all(dist.join("std")).unwrap();
    let bin = dist.join("bin/brass");
    fs::copy(env!("CARGO_BIN_EXE_brass"), &bin).unwrap();
    fs::write(
        dist.join("std/shipped.cz"),
        "fun greet() -> string { return \"shipped\" }\n",
    )
    .unwrap();
    let main = setup(
        "dist_layout_case",
        &[(
            "main.cz",
            "import std.shipped.{ greet }\nfun main() { println(greet()) }\n",
        )],
    );
    // Retried: a PARALLEL test thread fork+execing at the wrong moment
    // inherits the just-closed write fd of the `fs::copy` above between its
    // fork and exec, and executing `bin` then fails ETXTBSY until that child
    // execs. Transient by construction, so spin briefly.
    let out = (0..50)
        .find_map(|_| match Command::new(&bin).arg(&main).output() {
            Ok(out) => Some(out),
            Err(e) if e.raw_os_error() == Some(26) => {
                std::thread::sleep(std::time::Duration::from_millis(20));
                None
            }
            Err(e) => panic!("spawn dist brass: {e}"),
        })
        .expect("spawn dist brass (ETXTBSY persisted)");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "expected success, got: {stdout}{stderr}"
    );
    assert_eq!(stdout.trim(), "shipped", "{stdout}");
    // An explicit `std=...` declaration overrides the implicit binding.
    let other = setup_tree(
        "dist_layout_override",
        &[(
            "std/shipped.cz",
            "fun greet() -> string { return \"explicit\" }\n",
        )],
    );
    let out = Command::new(&bin)
        .arg(&main)
        .env("BRASS_PACKAGES", format!("std={}", other.display()))
        .output()
        .expect("spawn dist brass");
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
                "lib/consts.cz",
                "const VERSION = \"1.0.0\"\nconst MAX: int32 = 10\nconst LIMITS: int32[] = [1, 2]\nconst _SECRET = \"hidden\"\n",
            ),
            (
                "main.cz",
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
            ("lib/consts.cz", "const _SECRET = \"hidden\"\n"),
            (
                "main.cz",
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
                "lib/a.cz",
                "const MAX: int32 = 7\nfun a_max() -> int32 { return MAX }\n",
            ),
            (
                "lib/b.cz",
                "const MAX = \"seven\"\nfun b_max() -> string { return MAX }\n",
            ),
            (
                "main.cz",
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

/// A static call on a type whose NAME another module also declares (here: an
/// alias of that very type, `serv`'s `type HttpServer = Server` next to
/// `serve`'s nominal). The duplicate name qualifies both symbols, and every
/// bare-keyed lookup missed: the light pass typed `T.new(..)!` as unknown, the
/// caller lost its inferred fallibility, and importing the ALIAS anywhere in the
/// program broke a module that never referenced it.
#[test]
fn static_call_resolves_when_an_alias_shares_the_type_name() {
    let main = setup(
        "alias_name_collision",
        &[
            (
                "lib/lib.cz",
                "import lib.inner.{ T as Inner }\n\ntype T = Inner\n",
            ),
            (
                "lib/lib/inner.cz",
                concat!(
                    "type T = {\n    v: int32\n}\n\n",
                    "fun T.new(v: int32) {\n",
                    "    if v < 0 {\n        return error(\"negative\")\n    }\n",
                    "    return T { v: v }\n}\n",
                ),
            ),
            (
                "lib/lib/use.cz",
                "import inner.T\n\nfun make(v: int32) {\n    const t = T.new(v)!\n    return t\n}\n",
            ),
            (
                "main.cz",
                concat!(
                    "import lib.lib.use.{ make }\n",
                    "import lib.lib.{ T }\n\n",
                    "const t = make(1)!\n",
                    "println(t.v)\n",
                ),
            ),
        ],
    );
    let (ok, out) = run(&main);
    assert!(ok, "expected success, got: {out}");
    assert_eq!(out, "1\n", "{out}");
}

/// The `.czcache` life cycle: a clean run writes it next to the entry file; the
/// next run reuses it (and still prints the same output); editing a DEPENDENCY
/// invalidates it, and the changed program's output proves the rebuild really
/// happened rather than the stale cache answering.
#[test]
fn czcache_reuses_and_invalidates_on_dependency_change() {
    let main = setup(
        "czcache_cycle",
        &[
            ("lib/util.cz", "fun answer() -> int32 { return 40 }\n"),
            (
                "main.cz",
                "import lib.util.{ answer }\nfun main() { println(answer()) }\n",
            ),
        ],
    );
    let cache = main.with_extension("czcache");
    let run_cached = |main: &PathBuf| {
        let out = Command::new(env!("CARGO_BIN_EXE_brass"))
            .arg(main)
            .output()
            .expect("spawn brass");
        (
            out.status.success(),
            String::from_utf8_lossy(&out.stdout).into_owned(),
        )
    };

    let (ok, out) = run_cached(&main);
    assert!(ok, "cold run: {out}");
    assert_eq!(out, "40\n");
    assert!(cache.is_file(), "a clean run writes the cache");

    let (ok, out) = run_cached(&main);
    assert!(ok, "warm run: {out}");
    assert_eq!(out, "40\n", "the cached run answers identically");

    // Edit the dependency. The edit keeps the file's size, so it is the content
    // hash -- not the length, and no longer the mtime -- that has to catch it.
    fs::write(
        main.parent().unwrap().join("lib/util.cz"),
        "fun answer() -> int32 { return 42 }\n",
    )
    .unwrap();
    let (ok, out) = run_cached(&main);
    assert!(ok, "run after dependency edit: {out}");
    assert_eq!(out, "42\n", "the edited dependency must be recompiled");
}

/// A source file is keyed by its contents, so a rewrite that changes nothing --
/// which moves the mtime -- keeps the cache. This is what lets a `.czcache` be
/// distributed: unpacking a release archive gives every library file a fresh
/// mtime, and an mtime key would reject the shipped cache on every machine.
#[test]
fn czcache_survives_a_rewrite_with_identical_contents() {
    let util = "fun answer() -> int32 { return 40 }\n";
    let main = setup(
        "czcache_identical_rewrite",
        &[
            ("lib/util.cz", util),
            (
                "main.cz",
                "import lib.util.{ answer }\nfun main() { println(answer()) }\n",
            ),
        ],
    );
    // The perf log is the only place a hit is visible: a hit and a miss agree on
    // the program's output, which is the point of the cache.
    // `--eager` so the FULL cache write cannot race the lazy stop-at-exit.
    let run_logged = || {
        let out = Command::new(env!("CARGO_BIN_EXE_brass"))
            .arg("--eager")
            .arg(&main)
            .env("BRASS_LOG", "brass::perf=debug")
            .output()
            .expect("spawn brass");
        assert!(out.status.success());
        (
            String::from_utf8_lossy(&out.stdout).into_owned(),
            String::from_utf8_lossy(&out.stderr).into_owned(),
        )
    };

    run_logged();

    // Same bytes, new mtime -- the state a freshly unpacked file is in.
    fs::write(main.parent().unwrap().join("lib/util.cz"), util).unwrap();
    let (out, log) = run_logged();
    assert_eq!(out, "40\n");
    assert!(
        log.contains("cache-hit"),
        "an unchanged file must stay cached across a rewrite:\n{log}"
    );
}

/// A `.czcache` survives the project MOVING: stamps name sources relative to
/// the roots they were resolved under (entry directory, include roots), never
/// by machine path, so copying the whole tree -- project and include root both
/// -- to a different location still hits. This is the property that lets a
/// release ship caches alongside its libraries.
#[test]
fn czcache_survives_relocation() {
    let main = setup(
        "czcache_relocate",
        &[
            ("libs/util.cz", "fun answer() -> int32 { return 7 }\n"),
            (
                "app/main.cz",
                "import util.{ answer }\nfun main() { println(answer()) }\n",
            ),
        ],
    );
    let root = main.parent().unwrap().to_path_buf();
    let entry = root.join("app/main.cz");
    let run_at = |root: &PathBuf| {
        let out = Command::new(env!("CARGO_BIN_EXE_brass"))
            .arg(root.join("app/main.cz"))
            .env("BRASS_INCLUDE", root.join("libs"))
            .env("BRASS_LOG", "brass::perf=debug")
            .output()
            .expect("spawn brass");
        (
            out.status.success(),
            String::from_utf8_lossy(&out.stdout).into_owned(),
            String::from_utf8_lossy(&out.stderr).into_owned(),
        )
    };

    let (ok, out, err) = run_at(&root);
    assert!(ok, "cold run: {out} {err}");
    assert_eq!(out, "7\n");
    assert!(entry.with_extension("czcache").is_file());

    // Copy everything somewhere else; nothing at the old location is touched.
    let moved = root.with_file_name("czcache_relocate_moved");
    let _ = fs::remove_dir_all(&moved);
    copy_tree(&root, &moved);
    let (ok, out, err) = run_at(&moved);
    assert!(ok, "relocated run: {err}");
    assert_eq!(out, "7\n");
    assert!(
        err.contains("front/cache-hit"),
        "the moved project must reuse its cache: {err}"
    );

    // An edit at the NEW location misses -- content, not location, is the key.
    fs::write(
        moved.join("libs/util.cz"),
        "fun answer() -> int32 { return 8 }\n",
    )
    .unwrap();
    let (ok, out, err) = run_at(&moved);
    assert!(ok, "edited relocated run: {err}");
    assert_eq!(out, "8\n", "the edit must be recompiled");
}

/// Two entries share one cache path (`app` and `app.cz` both map to
/// `app.czcache`), so a hit requires the entry ITSELF to be the recorded one:
/// running the extensionless sibling must execute its own program, never the
/// cached neighbor's.
/// A LAZY run persists a cache too: the full payload when its checker
/// finished first, the partial (resume) payload when the exit stopped it.
/// Either way the file exists, and a rerun -- resumed or replayed -- prints
/// the same output. (Which flavor wins is a benign race; both are pinned
/// valid by the reruns.)
#[test]
fn lazy_runs_persist_and_reuse_a_cache() {
    let main = setup(
        "lazy_cache_reuse",
        &[(
            "main.cz",
            "fun greet(n: int32) -> int32 { return n + 1 }\nfun main() { println(greet(41)) }\n",
        )],
    );
    let run = || {
        let out = Command::new(env!("CARGO_BIN_EXE_brass"))
            .arg(&main)
            .output()
            .expect("spawn brass");
        assert!(
            out.status.success(),
            "stderr: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8_lossy(&out.stdout).into_owned()
    };
    let first = run();
    assert_eq!(first, "42\n");
    assert!(main.with_extension("czcache").is_file());
    assert_eq!(run(), first);
    assert_eq!(run(), first);
}

/// A full analysis cache skips the checker, but the default run must retain
/// entry-rooted JIT reachability: an unrelated zero-argument function is not
/// another compilation root merely because its signature needs no arguments.
#[test]
fn cached_lazy_run_compiles_only_entry_reachable_functions() {
    let main = setup(
        "cached_lazy_reachability",
        &[(
            "main.cz",
            "fun selected() -> int64 { return 42 }\n\
             fun skipped() -> int64 { return 141 }\n\
             fun main() { println(selected()) }\n",
        )],
    );

    // Produce a complete cache deterministically before exercising the lazy
    // cache-hit path; a short lazy first run may instead save a partial cache.
    let checked = Command::new(env!("CARGO_BIN_EXE_brass"))
        .arg("check")
        .arg(&main)
        .output()
        .expect("check program");
    assert!(
        checked.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&checked.stderr)
    );

    let out = Command::new(env!("CARGO_BIN_EXE_brass"))
        .arg(&main)
        .env("BRASS_LOG", "brass::perf=trace")
        .output()
        .expect("run cached program");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "stderr: {stderr}");
    assert_eq!(String::from_utf8_lossy(&out.stdout), "42\n");
    assert!(stderr.contains("front/cache-hit"), "stderr: {stderr}");
    let compiled: Vec<&str> = stderr
        .lines()
        .filter(|line| line.contains("back/codegen-fn:"))
        .collect();
    assert!(
        compiled.iter().any(|line| line.contains("selected")),
        "entry-reachable function was not compiled: {stderr}"
    );
    assert!(
        compiled.iter().all(|line| !line.contains("skipped")),
        "unreachable zero-argument function was compiled: {stderr}"
    );
}

/// Static reachability includes both arms of a runtime branch, but ORC should
/// optimize and emit native code only for the arm that execution enters.
#[test]
fn cached_lazy_run_materializes_only_the_executed_branch() {
    let main = setup(
        "cached_lazy_runtime_branch",
        &[(
            "main.cz",
            "fun selected() -> int64 { return 42 }\n\
             fun skipped() -> int64 { return 141 }\n\
             fun main() {\n\
                 if _argv().len() == 1 {\n\
                     println(selected())\n\
                 } else {\n\
                     println(skipped())\n\
                 }\n\
             }\n",
        )],
    );

    let checked = Command::new(env!("CARGO_BIN_EXE_brass"))
        .arg("check")
        .arg(&main)
        .output()
        .expect("check program");
    assert!(
        checked.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&checked.stderr)
    );

    let out = Command::new(env!("CARGO_BIN_EXE_brass"))
        .arg(&main)
        .env("BRASS_LOG", "brass::perf=trace")
        .output()
        .expect("run cached program");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "stderr: {stderr}");
    assert_eq!(String::from_utf8_lossy(&out.stdout), "42\n");
    let materialized: Vec<&str> = stderr
        .lines()
        .filter(|line| line.contains("back/orc-materialize"))
        .collect();
    assert!(
        materialized
            .iter()
            .any(|line| line.contains("pp_fn_selected")),
        "executed branch was not materialized: {stderr}"
    );
    assert!(
        materialized
            .iter()
            .all(|line| !line.contains("pp_fn_skipped")),
        "unexecuted runtime branch was materialized: {stderr}"
    );
}

/// A spawning program precompiles exactly what its workers can statically
/// reach (spawned closures and their call graphs, before the spawn runs);
/// main-thread-only code keeps demand-driven materialization, so a dead main
/// branch is still never compiled.
#[test]
fn cached_lazy_spawn_precompiles_only_worker_reachable_code() {
    let main = setup(
        "cached_lazy_spawn_reachability",
        &[(
            "main.cz",
            "fun worker_task() -> int64 { return 7 }\n\
             fun main_selected() -> int64 { return 42 }\n\
             fun main_skipped() -> int64 { return 141 }\n\
             fun main() {\n\
                 let base = 100\n\
                 spawn(() -> { println(worker_task() + base) })\n\
                 sync()\n\
                 if _argv().len() == 1 {\n\
                     println(main_selected())\n\
                 } else {\n\
                     println(main_skipped())\n\
                 }\n\
             }\n",
        )],
    );

    let checked = Command::new(env!("CARGO_BIN_EXE_brass"))
        .arg("check")
        .arg(&main)
        .output()
        .expect("check program");
    assert!(
        checked.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&checked.stderr)
    );

    let out = Command::new(env!("CARGO_BIN_EXE_brass"))
        .arg(&main)
        .env("BRASS_LOG", "brass::perf=trace")
        .output()
        .expect("run cached program");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "stderr: {stderr}");
    assert_eq!(String::from_utf8_lossy(&out.stdout), "107\n42\n");
    let materialized: Vec<&str> = stderr
        .lines()
        .filter(|line| line.contains("back/orc-materialize"))
        .collect();
    assert!(
        materialized
            .iter()
            .any(|line| line.contains("pp_fn_worker_5f_task")),
        "worker-reachable function was not materialized: {stderr}"
    );
    assert!(
        materialized
            .iter()
            .any(|line| line.contains("pp_fn_main_5f_selected")),
        "executed main branch was not materialized: {stderr}"
    );
    assert!(
        materialized
            .iter()
            .all(|line| !line.contains("pp_fn_main_5f_skipped")),
        "main-only dead branch was materialized despite the spawn: {stderr}"
    );
}

#[test]
fn czcache_is_entry_specific() {
    let main = setup(
        "czcache_entry_identity",
        &[
            ("app.cz", "fun main() { println(\"from app.cz\") }\n"),
            ("app", "fun main() { println(\"from app\") }\n"),
            ("main.cz", "fun main() {}\n"),
        ],
    );
    let root = main.parent().unwrap().to_path_buf();
    // `--eager`: a lazy run stops the checker when the program ends, so
    // whether the FULL cache gets written races the (tiny) program. The
    // cache-identity property under test is mode-independent.
    let run = |entry: &PathBuf| {
        let out = Command::new(env!("CARGO_BIN_EXE_brass"))
            .arg("--eager")
            .arg(entry)
            .output()
            .expect("spawn brass");
        (
            out.status.success(),
            String::from_utf8_lossy(&out.stdout).into_owned(),
        )
    };

    let (ok, out) = run(&root.join("app.cz"));
    assert!(ok, "cold run: {out}");
    assert_eq!(out, "from app.cz\n");
    assert!(root.join("app.czcache").is_file());

    let (ok, out) = run(&root.join("app"));
    assert!(ok, "sibling run: {out}");
    assert_eq!(
        out, "from app\n",
        "the extensionless sibling must not revive app.cz's cached program"
    );
}

/// A newly declared `BRASS_PACKAGES` name captures an import's first segment
/// BEFORE any file search, re-routing the import while every stamped file is
/// untouched; the recorded name set must catch it and recompile.
#[test]
fn czcache_misses_when_package_names_change() {
    let main = setup(
        "czcache_pkg_rebind",
        &[
            ("util/helpers.cz", "fun answer() -> int32 { return 1 }\n"),
            (
                "main.cz",
                "import util.helpers.{ answer }\nfun main() { println(answer()) }\n",
            ),
            (
                "dep/util/helpers.cz",
                "fun answer() -> int32 { return 2 }\n",
            ),
        ],
    );
    let root = main.parent().unwrap().to_path_buf();
    let run = |packages: Option<String>| {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_brass"));
        cmd.arg(&main);
        if let Some(p) = packages {
            cmd.env("BRASS_PACKAGES", p);
        }
        let out = cmd.output().expect("spawn brass");
        (
            out.status.success(),
            String::from_utf8_lossy(&out.stdout).into_owned(),
        )
    };

    let (ok, out) = run(None);
    assert!(ok, "cold run: {out}");
    assert_eq!(out, "1\n", "no package declared: the local file answers");

    let (ok, out) = run(Some(format!("util={}", root.join("dep").display())));
    assert!(ok, "package-bound run: {out}");
    assert_eq!(
        out, "2\n",
        "declaring the package re-routes the import; the cache must not answer with the local file"
    );
}

/// `_PATH` is the one thing a relocated cache must NOT replay: it IS the
/// module's location. A hit after the project moves re-anchors it while the
/// analysis itself stays cached.
#[test]
fn czcache_reanchors_module_path_on_relocation() {
    let main = setup(
        "czcache_path_reanchor",
        &[
            (
                "whereami.cz",
                "fun where_am_i() -> string { return _PATH }\n",
            ),
            (
                "main.cz",
                "import whereami.{ where_am_i }\nfun main() { println(where_am_i()) }\n",
            ),
        ],
    );
    let root = main.parent().unwrap().to_path_buf();
    let run_at = |root: &PathBuf| {
        let out = Command::new(env!("CARGO_BIN_EXE_brass"))
            .arg(root.join("main.cz"))
            .env("BRASS_LOG", "brass::perf=debug")
            .output()
            .expect("spawn brass");
        (
            out.status.success(),
            String::from_utf8_lossy(&out.stdout).into_owned(),
            String::from_utf8_lossy(&out.stderr).into_owned(),
        )
    };

    let (ok, out, err) = run_at(&root);
    assert!(ok, "cold run: {out} {err}");
    assert!(out.contains("whereami.cz"), "{out}");

    let moved = root.with_file_name("czcache_path_reanchor_moved");
    let _ = fs::remove_dir_all(&moved);
    copy_tree(&root, &moved);
    let (ok, out, err) = run_at(&moved);
    assert!(ok, "relocated run: {err}");
    assert!(
        err.contains("front/cache-hit"),
        "the moved project must reuse its cache: {err}"
    );
    let moved_canon = moved.canonicalize().unwrap();
    assert!(
        out.contains(&moved_canon.display().to_string()),
        "_PATH must point at the module's NEW location, got: {out}"
    );
}

/// Recursive copy for the relocation test (no external crates).
fn copy_tree(from: &PathBuf, to: &PathBuf) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let src = entry.path();
        let dst = to.join(entry.file_name());
        if src.is_dir() {
            copy_tree(&src, &dst);
        } else {
            fs::copy(&src, &dst).unwrap();
        }
    }
}

/// The context seed: after a cold run stores the context's inference tables
/// (everything except the entry), an ENTRY edit re-infers only the entry --
/// and must still see the edit, not the cached program. The seed store is
/// isolated via XDG_CACHE_HOME so the test cannot touch the user's.
#[test]
fn context_seed_survives_entry_edits() {
    let main = setup(
        "ctx_seed_entry_edit",
        &[
            (
                "lib/util.cz",
                "fun double(v: int32) -> int32 { return v * 2 }\n",
            ),
            (
                "main.cz",
                "import lib.util.{ double }\nfun main() { println(double(3)) }\n",
            ),
        ],
    );
    let cache_home = main.parent().unwrap().join("xdg-cache");
    let run = |main: &PathBuf| {
        let out = Command::new(env!("CARGO_BIN_EXE_brass"))
            .arg(main)
            .env("XDG_CACHE_HOME", &cache_home)
            .output()
            .expect("spawn brass");
        (
            out.status.success(),
            String::from_utf8_lossy(&out.stdout).into_owned(),
            String::from_utf8_lossy(&out.stderr).into_owned(),
        )
    };

    let (ok, out, err) = run(&main);
    assert!(ok, "cold: {err}");
    assert_eq!(out, "6\n");
    let seeds = cache_home.join("brass");
    assert!(
        seeds.is_dir() && fs::read_dir(&seeds).unwrap().next().is_some(),
        "the cold run stores a context seed"
    );

    // Edit the ENTRY: the context seed still applies, and the result reflects
    // the edit (the entry really was re-checked, only the context was not).
    fs::write(
        &main,
        "import lib.util.{ double }\nfun main() { println(double(5)) }\n",
    )
    .unwrap();
    let (ok, out, err) = run(&main);
    assert!(ok, "entry edit: {err}");
    assert_eq!(out, "10\n");

    // Edit the CONTEXT: the seed is stale by key, so the change is honored too.
    fs::write(
        main.parent().unwrap().join("lib/util.cz"),
        "fun double(v: int32) -> int32 { return v * 3 }\n",
    )
    .unwrap();
    let (ok, out, err) = run(&main);
    assert!(ok, "context edit: {err}");
    assert_eq!(out, "15\n");
}
