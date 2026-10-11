//! Diagnostic parity at lazy entry and runtime compilation gates.

mod support;

use std::fs;
use std::path::PathBuf;
use std::process::Output;
use std::sync::atomic::{AtomicUsize, Ordering};

struct Fixture {
    root: PathBuf,
}

impl Fixture {
    fn new(source: &str) -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!(
            "lazy-diagnostics-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        fs::create_dir_all(&root).expect("create fixture");
        fs::write(root.join("main.cz"), source).expect("write fixture");
        Self { root }
    }

    fn run(&self, mode: Option<&str>) -> Output {
        let mut command = support::brass_command(env!("CARGO_BIN_EXE_brass"));
        command.args(mode).arg(self.root.join("main.cz"));
        command.output().expect("run diagnostic fixture")
    }

    fn rejects(&self, expected: &[&str], lazy_stdout: &str) {
        let check = self.run(Some("check"));
        assert!(!check.status.success(), "check must reject the fixture");
        let diagnostics = String::from_utf8_lossy(&check.stderr);
        for message in expected {
            assert!(diagnostics.contains(message), "{message:?}: {diagnostics}");
        }
        for mode in [None, Some("--eager")] {
            let output = self.run(mode);
            assert!(!output.status.success(), "{mode:?} must reject the fixture");
            assert_eq!(
                String::from_utf8_lossy(&output.stdout),
                if mode.is_none() && cfg!(feature = "jit") {
                    lazy_stdout
                } else {
                    ""
                },
                "{mode:?} must stop before the rejected code runs",
            );
            assert_eq!(
                String::from_utf8_lossy(&output.stderr),
                diagnostics,
                "{mode:?} must render the checker's complete diagnostic text and spans",
            );
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

#[test]
fn called_method_pattern_stops_before_method_effects() {
    // The pattern token owns the error; no print in the rejected method runs.
    Fixture::new(
        "type T = {}\nfun T.m(self) {\n println(\"rejected method\")\n let 5 = 5\n}\n\
         fun main() { T {}.m() }\n",
    )
    .rejects(
        &[":4:6: error: refutable pattern in `let`; use `if let` or `match`"],
        "",
    );
}

#[test]
#[cfg(feature = "jit")]
fn uncalled_function_patterns_remain_lazy() {
    // Whole-program modes retain every diagnostic while lazy execution ignores
    // the unused body, including a refutable let and its precise source span.
    let fixture =
        Fixture::new("fun unused() { let 5 = 5 }\nfun main() { println(\"called body\") }\n");
    let output = fixture.run(None);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(output.stdout, b"called body\n");
    assert!(output.stderr.is_empty(), "{output:?}");
    for mode in ["check", "--eager"] {
        let output = fixture.run(Some(mode));
        assert!(!output.status.success(), "{mode}: {output:?}");
        assert!(output.stdout.is_empty(), "{mode}: {output:?}");
        assert!(
            String::from_utf8_lossy(&output.stderr)
                .contains(":1:20: error: refutable pattern in `let`; use `if let` or `match`")
        );
    }
}

#[test]
fn pattern_contracts_gate_each_needed_body_kind() {
    // All contracts use the same gate in functions, methods, closures and
    // module initializers. Notes must survive the full checker in every scope.
    let contracts = [
        ("let 5 = 5", "refutable pattern in `let`"),
        ("const 5 = 5", "refutable pattern in `const`"),
        ("for 5 in [5] {}", "refutable pattern in `for`"),
        (
            "let [x, x] = [1, 2]",
            "`x` is bound more than once in this pattern",
        ),
        (
            "match Color.Red { Rde => 1, Green => 2 }",
            "did you mean the variant `Red`?",
        ),
        (
            "const LIMIT = 1\nmatch 1 { LIMIT => 1, _ => 2 }",
            "does not compare with the constant `LIMIT`",
        ),
    ];
    for (contract, diagnostic) in contracts {
        let body = format!("println(\"rejected body\")\n{contract}");
        for source in [
            format!("fun bad() {{ {body} }}\nfun main() {{ bad() }}"),
            format!("type T = {{}}\nfun T.bad(self) {{ {body} }}\nfun main() {{ T {{}}.bad() }}"),
            format!("fun main() {{ let f = () -> {{ {body} }}\nf() }}"),
            body,
        ] {
            Fixture::new(&format!("type Color = Red | Green\n{source}\n"))
                .rejects(&[diagnostic], "");
        }
    }
}

#[test]
fn deferred_pattern_error_stops_before_the_called_body() {
    // A later method batch may run after earlier output, but never after an
    // effect in either the rejected method or its newly compiled caller.
    Fixture::new(
        "type T = {}\nfun T.m(self) { println(\"rejected method\")\n let 5 = 5 }\n\
         fun later() -> void { println(\"rejected caller\")\n T {}.m() }\n\
         fun main() { println(\"before\")\n later() }\n",
    )
    .rejects(&["refutable pattern in `let`"], "before\n");
}

#[test]
#[cfg(feature = "jit")]
fn uncalled_method_patterns_remain_lazy() {
    // A method is needed only by its compiled batch, even when its body was
    // checked during shared context construction.
    let fixture = Fixture::new(
        "type T = {}\nfun T.unused(self) { let 5 = 5 }\n\
         fun main() { println(\"called body\") }\n",
    );
    let output = fixture.run(None);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(output.stdout, b"called body\n");
    assert!(output.stderr.is_empty(), "{output:?}");
    for mode in ["check", "--eager"] {
        let output = fixture.run(Some(mode));
        assert!(!output.status.success(), "{mode}: {output:?}");
        assert!(output.stdout.is_empty(), "{mode}: {output:?}");
        assert!(String::from_utf8_lossy(&output.stderr).contains("refutable pattern in `let`"));
    }
}

#[test]
fn imported_initializer_patterns_gate_entry() {
    // Imported top-level patterns are always needed, even with no imported call.
    let fixture = Fixture::new("import bad\nfun main() { println(\"rejected entry\") }\n");
    fs::write(fixture.root.join("bad.cz"), "let 5 = 5\n").expect("write initializer");
    fixture.rejects(&["bad.cz:1:5: error: refutable pattern in `let`"], "");
}

#[test]
fn uninstantiated_templates_and_pruned_branches_follow_ordinary_rules() {
    // Pattern checking follows the full checker's template and branch selection.
    let fixture = Fixture::new(include_str!(
        "../../../e2e_tests/parser_review/unselected_patterns.cz"
    ));
    for mode in [Some("check"), Some("--eager"), None] {
        let output = fixture.run(mode);
        assert!(output.status.success(), "{mode:?}: {output:?}");
        assert!(output.stderr.is_empty(), "{mode:?}: {output:?}");
        assert_eq!(
            output.stdout,
            if mode == Some("check") {
                &b""[..]
            } else {
                &b"selected body\n"[..]
            }
        );
    }
}

#[test]
fn duplicate_method_parameter_stops_before_entry() {
    // Both checker paths reject the second named parameter before execution.
    Fixture::new(
        "type T = { v: int32 }\n\
         fun T.m(self, x, x) {\n    return self.v\n}\n\
         fun main() {\n\
             println(\"user code\")\n\
             let t = T { v: 1 }\n\
             let u = T { v: 2 }\n\
             println(t.m(u, u))\n\
         }\n",
    )
    .rejects(
        &[
            ":2:18: error: duplicate parameter `x` in method\n",
            ":2:18: error: duplicate parameter `x` in method `T.m`",
        ],
        "",
    );
}

#[test]
fn receiver_body_errors_precede_native_compilation() {
    // sf1: self is T in the checker; retain both source diagnostics, not an LLVM error.
    Fixture::new(
        "type T = { v: int32 }\n\
         fun T.m(self: int32) {\n    return self + 1\n}\n\
         fun main() {\n\
             println(\"user code\")\n\
             let t = T { v: 5 }\n\
             println(t.m())\n\
         }\n",
    )
    .rejects(
        &[
            ":3:12: error: operator `+` is not defined for `T` and `int32` (no applicable conversion)",
            ":3:19: error: integer literal used where `T` is required",
        ],
        "",
    );
}

#[test]
fn method_parameter_modes_gate_execution() {
    // The const pass's read-only parameter error can survive native lowering.
    Fixture::new(
        "type T = { v: int32 }\n\
         fun T.m(self, xs: ref(int32[])) { xs.push(1) }\n\
         fun main() { println(\"user code\")\n T { v: 1 }.m([]) }\n",
    )
    .rejects(
        &["cannot call mutating method `push` on const value `xs`"],
        "",
    );
}

#[test]
fn method_annotation_resolution_gates_execution() {
    // A signature annotation is rejected even if the parameter is never read.
    Fixture::new(
        "type T = { v: int32 }\n\
         fun T.m(self, value: Missing) { println(1) }\n\
         fun main() { println(\"user code\")\n T { v: 1 }.m(2) }\n",
    )
    .rejects(&["unknown type `Missing`"], "");
}

#[test]
fn method_control_flow_gates_execution() {
    // The return-path error points at the signature, outside the method block.
    Fixture::new(
        "type T = { v: int32 }\n\
         fun T.m(self, c: bool) -> int32 { if c { return 1 } }\n\
         fun main() { println(\"user code\")\n println(T { v: 1 }.m(true)) }\n",
    )
    .rejects(
        &["function `m` may finish without returning a value of type `int32`"],
        "",
    );
}

#[test]
fn method_definite_assignment_gates_execution() {
    // A method's uninitialized read must be rejected by the source checker.
    Fixture::new(
        "type T = { v: int32 }\n\
         fun T.m(self) { let x: int32\n println(x) }\n\
         fun main() { println(\"user code\")\n T { v: 1 }.m() }\n",
    )
    .rejects(&["`x` is used before it is fully initialized"], "");
}

#[test]
fn method_untaken_branch_is_still_checked() {
    // HM errors in an untaken branch belong to the complete called body.
    Fixture::new(
        "type T = { v: int32 }\n\
         fun T.m(self) { if false { let x: int32 = \"bad\" } }\n\
         fun main() { println(\"user code\")\n T { v: 1 }.m() }\n",
    )
    .rejects(&["int32", "string"], "");
}

#[test]
fn concrete_method_match_is_checked_before_entry() {
    // The open method pass cannot identify S; the concrete call must check coverage.
    Fixture::new(
        "type S = | A | B\n\
         type T = { v: int32 }\n\
         fun T.m(self, s) { match s { A => println(\"A\") } }\n\
         fun main() { println(\"user code\")\n T { v: 1 }.m(S.A) }\n",
    )
    .rejects(&["non-exhaustive match on `S`: missing variant(s) B"], "");
}

#[test]
fn sum_method_signature_gates_execution() {
    // The shared method declaration appears in each variant's HIR method table.
    Fixture::new(
        "type S = | A | B\n\
         fun S.m(self, x, x) { return 2 }\n\
         fun main() { println(\"user code\")\n println(S.A.m(S.B, S.B)) }\n",
    )
    .rejects(&["duplicate parameter `x` in method"], "");
}

#[test]
fn deferred_method_errors_stop_before_that_body() {
    // A method first compiled inside a deferred free function uses the runtime gate.
    Fixture::new(
        "type T = { v: int32 }\n\
         fun T.m(self) { if false { let x: int32 = \"bad\" } }\n\
         fun later() -> void { println(\"rejected caller\")\n T { v: 1 }.m() }\n\
         fun main() { println(\"before\")\n later() }\n",
    )
    .rejects(&["int32", "string"], "before\n");
}

#[test]
fn deferred_lowering_failure_keeps_the_checker_diagnostic() {
    // A failed batch has no method instances to mark; its source error still wins.
    Fixture::new(
        "type T = { v: int32 }\n\
         fun T.m(self, xs: ref(int32[])) { xs.push(1) }\n\
         fun later() -> void { T { v: 1 }.m([]) }\n\
         fun main() { println(\"before\")\n later() }\n",
    )
    .rejects(
        &["cannot call mutating method `push` on const value `xs`"],
        "before\n",
    );
}

#[test]
fn unresolved_error_return_gates_execution() {
    // A body-local return contract must not wait for the whole-program terminal pass.
    Fixture::new(
        "fun f(c: bool) -> int32! { if c { return f(c)! }\n return 1 }\n\
         fun main() { println(\"user code\")\n println(f(false)!) }\n",
    )
    .rejects(&["cannot infer the error type of `!`"], "");
}

#[test]
fn runtime_specialization_preserves_the_checker_verdict() {
    // Beyond the re-elaboration depth limit, the key is discovered at runtime.
    // A rejected generated continuation must report source errors, not an
    // incomplete-demand error or instructions to rerun a rejected program.
    let mut source = String::from(
        "type T = {}\nfun T.into(self) -> infer! { return \"bad\" }\n\
         fun f70() -> int32 { let n: int32 = T {}.into()!\n return n }\n",
    );
    for index in 0..70 {
        source.push_str(&format!(
            "fun f{index}() -> int32 {{ return f{}() }}\n",
            index + 1,
        ));
    }
    source.push_str("fun main() { println(\"before\")\n println(f0()) }\n");
    Fixture::new(&source).rejects(
        &[
            "cannot use `string` where `int32` is required",
            "error propagation requires `Result` return type, found `int32`",
        ],
        "before\n",
    );
}

#[test]
fn interface_conformance_gates_execution() {
    // Interface signature conformance is a static error before any body runs.
    Fixture::new(
        "type I = { m(self, x: string) -> void }\n\
         type T: I = {}\n\
         fun T.m(self, x: int32) -> void {}\n\
         fun main() { println(\"user code\") }\n",
    )
    .rejects(&["method `m` signature is not compatible with `I`"], "");
}

#[test]
fn duplicate_declarations_gate_execution() {
    // Lowering errors abort before entry, even when a duplicate would be overwritten.
    Fixture::new(
        "fun f() { return 1 }\nfun f() { return 2 }\n\
         fun main() { println(\"user code\") }\n",
    )
    .rejects(&["duplicate"], "");
}

#[test]
fn uncalled_signature_errors_are_checked_up_front() {
    // Duplicate parameters reject the shared signature even without a body demand.
    Fixture::new(
        "fun unused(x, x) { return x }\n\
         fun main() { println(\"user code\") }\n",
    )
    .rejects(&["duplicate parameter `x`"], "");
}

#[test]
fn import_resolution_errors_gate_execution() {
    // Import validation is published before initializer or main readiness.
    let fixture = Fixture::new("import lib.{ missing }\nfun main() { println(\"user code\") }\n");
    fs::write(fixture.root.join("lib.cz"), "fun present() { return 1 }\n")
        .expect("write imported module");
    fixture.rejects(&["module `lib` has no exported name `missing`"], "");
}

#[test]
fn static_method_errors_gate_execution() {
    // Static calls use the same method ownership gate as value-receiver calls.
    Fixture::new(
        "type T = {}\nfun T.m() { if false { let x: int32 = \"bad\" } }\n\
         fun main() { println(\"user code\")\n T.m() }\n",
    )
    .rejects(&["int32", "string"], "");
}

#[test]
fn initializer_method_errors_gate_execution_without_main() {
    // The entry gate also covers methods compiled for module initialization alone.
    Fixture::new(
        "type T = {}\nfun T.m(self) { if false { let x: int32 = \"bad\" } }\n\
         println(\"user code\")\nT {}.m()\n",
    )
    .rejects(&["int32", "string"], "");
}

#[test]
fn top_level_errors_gate_execution_without_main() {
    // All initializer statements must settle before even the first print executes.
    Fixture::new("println(\"user code\")\nlet x: int32 = \"bad\"\n")
        .rejects(&["int32", "string"], "");
}

#[test]
fn imported_initializer_errors_gate_entry() {
    // Every module initializer is an entry gate, not just the entry file's statements.
    let fixture = Fixture::new("import bad\nfun main() { println(\"user code\") }\n");
    fs::write(fixture.root.join("bad.cz"), "let x: int32 = \"bad\"\n")
        .expect("write imported initializer");
    fixture.rejects(&["int32", "string"], "");
}

#[test]
fn main_errors_gate_execution() {
    // The entry function's complete body must pass before its first effect.
    Fixture::new("fun main() { println(\"user code\")\n let x: int32 = \"bad\" }\n")
        .rejects(&["int32", "string"], "");
}

#[test]
#[cfg(feature = "jit")]
fn uncalled_method_errors_remain_lazy_across_modules() {
    // Same-named types in different modules must not share diagnostic ownership.
    let fixture = Fixture::new(
        "import bad\nimport good\n\
         fun main() { let t = good.T { v: 1 }\n println(t.m()) }\n",
    );
    fs::write(
        fixture.root.join("bad.cz"),
        "type T = { v: int32 }\nfun T.m(self) -> int32 { return \"bad\" }\n",
    )
    .expect("write uncalled method");
    fs::write(
        fixture.root.join("good.cz"),
        "type T = { v: int32 }\nfun T.m(self) -> int32 { return self.v }\n",
    )
    .expect("write called method");
    let output = fixture.run(None);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"1\n");
    assert!(!fixture.run(Some("check")).status.success());
    assert!(!fixture.run(Some("--eager")).status.success());
}
