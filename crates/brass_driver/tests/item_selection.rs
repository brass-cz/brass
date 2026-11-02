//! Body selection preserves catalog diagnostics and complete own-file checking.

mod support;

use std::fs;
use std::path::PathBuf;

struct Fixture(PathBuf);

impl Fixture {
    fn new(name: &str, dependency: &str, entry: &str) -> Self {
        let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("item-selection-{}-{name}", std::process::id()));
        fs::create_dir_all(root.join("dep")).unwrap();
        fs::write(root.join("dep/lib.cz"), dependency).unwrap();
        fs::write(root.join("main.cz"), entry).unwrap();
        Self(root)
    }

    fn run(&self, eager: bool) -> std::process::Output {
        support::brass_command(env!("CARGO_BIN_EXE_brass"))
            .env("BRASS_PACKAGES", format!("dep={}", self.0.display()))
            .env_remove("BRASS_LOG")
            .arg(if eager { "--eager" } else { "check" })
            .arg(self.0.join("main.cz"))
            .output()
            .unwrap()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn uncalled_dependency_writer_keeps_initializer_inference() {
    // An initializer is reached even when its only typing contributor is not
    // called. Selection must preserve the shared global cell, not fabricate a
    // type for the empty array or suppress its diagnostic.
    let fixture = Fixture::new(
        "global",
        "let values = []\nfun writer() { values.push(1) }\nfun reached() { return values.len() }",
        "import dep.lib.{ reached }\nlet count = reached()",
    );
    {
        let result = fixture.run(false);
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
}

#[test]
fn omitted_dependency_errors_and_reached_siblings() {
    // The invalid body is visible through its declaration, but only a real use
    // schedules its body. Own unused bodies remain roots in every mode.
    let dependency = "fun good() -> int32 { return 1 }\nfun bad() -> int32 { return false }";
    let fixture = Fixture::new(
        "unused",
        dependency,
        "import dep.lib.{ good }\nlet answer = good()",
    );
    let selected = fixture.run(false);
    assert!(
        selected.status.success(),
        "{}",
        String::from_utf8_lossy(&selected.stderr)
    );
    fs::write(
        fixture.0.join("main.cz"),
        "import dep.lib.{ bad }\nfun own_unused() { return bad() }",
    )
    .unwrap();
    assert!(!fixture.run(false).status.success());
}

#[test]
fn recovered_body_and_catalog_boundary_are_distinct() {
    // A recovered body with intact declaration delimiters can be omitted. A
    // broken declaration boundary remains a catalog error in every mode.
    let fixture = Fixture::new(
        "syntax",
        "fun good() -> int32 { return 1 }\nfun bad() { let x =\nreturn 1\n}",
        "import dep.lib.{ good }\nlet answer = good()",
    );
    let selected = fixture.run(false);
    assert!(
        selected.status.success(),
        "{}",
        String::from_utf8_lossy(&selected.stderr)
    );
    fs::write(
        fixture.0.join("dep/lib.cz"),
        "fun good() -> int32 { return 1 }\nfun bad( {",
    )
    .unwrap();
    assert!(!fixture.run(false).status.success());
}

#[test]
fn qualified_body_diagnostics_follow_selection_in_check_and_eager() {
    // Name rewriting must see the complete import catalog before selection; the
    // resulting body-local diagnostic belongs only to the omitted function.
    let fixture = Fixture::new(
        "qualified",
        "import dep.other\nfun good() -> int32 { return 1 }\nfun unused() { return other.missing() }",
        "import dep.lib.{ good }\nlet answer = good()",
    );
    fs::write(
        fixture.0.join("dep/other.cz"),
        "fun exists() -> int32 { return 2 }",
    )
    .unwrap();
    for eager in [false, true]
        .into_iter()
        .filter(|eager| !eager || cfg!(feature = "jit"))
    {
        let selected = fixture.run(eager);
        assert!(
            selected.status.success(),
            "{}",
            String::from_utf8_lossy(&selected.stderr)
        );
    }
}

#[test]
fn omitted_bodies_are_not_lowered_in_either_execution_policy() {
    // Keep the erroneous declarations visible, including a rootless sum method.
    // Selection must prevent their body diagnostics AND their MIR/LLVM lowering.
    let fixture = Fixture::new(
        "selected-execution",
        "type Choice = | A | B\nfun Choice.bad(self) -> int32 { return false }\nfun good() -> int32 { return 7 }\nfun bad() -> int32 { return false }",
        "import dep.lib.{ good, Choice }\nlet value = Choice.A\nprintln(good())",
    );
    for complete in ["auto", "off"] {
        for mode in ["check", "eager", "lazy"] {
            let mut command = support::brass_command(env!("CARGO_BIN_EXE_brass"));
            command
                .env("BRASS_LAZY_COMPLETE", complete)
                .env("BRASS_PACKAGES", format!("dep={}", fixture.0.display()))
                .env_remove("BRASS_LOG");
            match mode {
                "check" => {
                    command.arg("check");
                }
                "eager" => {
                    command.arg("--eager");
                }
                _ => {}
            }
            let result = command.arg(fixture.0.join("main.cz")).output().unwrap();
            assert!(
                result.status.success(),
                "{mode}/{complete}: {}",
                String::from_utf8_lossy(&result.stderr)
            );
            assert!(result.stderr.is_empty());
            assert_eq!(
                result.stdout,
                if mode == "check" {
                    &b""[..]
                } else {
                    &b"7\n"[..]
                }
            );
        }
    }
}

#[test]
fn generated_dependencies_close_before_the_entry_gate() {
    // The generated root checks an open receiver frame even when its execution
    // call supplies int32. Its rendering family must already be prepared. The
    // retained Result also exercises synthesized error/Location dependencies
    // without relying on entry error propagation to select them.
    for (name, dependency, expected) in [
        (
            "open-keyed",
            "type Box = { value }\nfun Box.conv(self) -> infer! { println(self.value)\nreturn infer.from(7) }\ntype Hidden = | A\nfun Hidden.display(self) -> string { return \"hidden\" }",
            &b"7\n9\n"[..],
        ),
        (
            "closed-keyed",
            "type Box = { value: int32 }\nfun Box.conv(self) -> infer! { return infer.from(self.value) }",
            &b"9\n"[..],
        ),
    ] {
        let fixture = Fixture::new(
            name,
            dependency,
            "import dep.lib.{ Box }\nfun main() { let result: int32! = Box { value: 7 }.conv()\nprintln(9) }",
        );
        for complete in ["auto", "off"] {
            for mode in ["check", "eager", "lazy"] {
                let mut command = support::brass_command(env!("CARGO_BIN_EXE_brass"));
                command
                    .env("BRASS_LAZY_COMPLETE", complete)
                    .env("BRASS_PACKAGES", format!("dep={}", fixture.0.display()))
                    .env_remove("BRASS_LOG");
                match mode {
                    "check" => {
                        command.arg("check");
                    }
                    "eager" => {
                        command.arg("--eager");
                    }
                    _ => {}
                }
                let result = command.arg(fixture.0.join("main.cz")).output().unwrap();
                assert!(
                    result.status.success(),
                    "{name}/{mode}/{complete}: {}",
                    String::from_utf8_lossy(&result.stderr)
                );
                assert!(
                    result.stderr.is_empty(),
                    "{}",
                    String::from_utf8_lossy(&result.stderr)
                );
                assert_eq!(
                    result.stdout,
                    if mode == "check" { &b""[..] } else { expected }
                );
            }
        }
    }
}

#[test]
fn core_only_skips_selection_but_disk_imports_do_not() {
    // Only the embedded core takes the complete-context shortcut. A std import
    // must still construct selection even when none of its bodies are called.
    let fixture = Fixture::new("core-shortcut", "", "println(7)");
    for (source, selected) in [
        ("println(7)", false),
        ("import std.data.json.{ JsonValue }\nprintln(7)", true),
    ] {
        fs::write(fixture.0.join("main.cz"), source).unwrap();
        let result = support::brass_command(env!("CARGO_BIN_EXE_brass"))
            .env(
                "BRASS_PACKAGES",
                format!(
                    "std={}",
                    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                        .join("../..")
                        .display()
                ),
            )
            .env("BRASS_LOG", "brass::item_cost=debug")
            .arg("check")
            .arg(fixture.0.join("main.cz"))
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&result.stderr).contains("phase=\"catalog\""),
            selected
        );
    }
}

#[test]
fn repl_extends_dependency_selection_without_replaying_effects() {
    use std::io::Write;
    use std::process::Stdio;
    let fixture = Fixture::new(
        "repl",
        "fun good() -> int32 { return 7 }\nfun bad() -> int32 { return false }",
        "",
    );
    let mut child = support::brass_command(env!("CARGO_BIN_EXE_brass"))
        .env("BRASS_PACKAGES", format!("dep={}", fixture.0.display()))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    // The unused bad declaration must not reject the import. A later own
    // definition reaches it and is rejected, without printing earlier effects.
    child.stdin.take().unwrap().write_all(b"import dep.lib.{ good, bad }\nprintln(good())\nfun own_unused() { return bad() }\nprintln(9)\n").unwrap();
    let output = child.wait_with_output().unwrap();
    assert_eq!(
        output.stdout,
        b"7\n9\n",
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stderr).contains("error:"));
}

#[test]
fn nested_debug_is_reached_but_an_unused_dependency_debug_is_not_checked() {
    let fixture = Fixture::new(
        "nested-debug",
        "type Used = | Value\nfun Used.debug(self) -> string { return \"selected\" }\ntype Unused = | Value\nfun Unused.debug(self) -> string { return false }",
        "import dep.lib.{ Used }\ntype Holder = { value: Used }\nprintln(Holder { value: Used.Value })",
    );
    // Package provenance is essential: local-route imports are own code and
    // deliberately check every body in eager/check modes.
    for used in [false, true] {
        if used {
            fs::write(
                fixture.0.join("main.cz"),
                "import dep.lib.{ Unused }\nprintln([Unused.Value])",
            )
            .unwrap();
        }
        for mode in ["check", "eager", "lazy", "repl"] {
            let mut command = support::brass_command(env!("CARGO_BIN_EXE_brass"));
            command
                .env("BRASS_PACKAGES", format!("dep={}", fixture.0.display()))
                .env_remove("BRASS_LOG");
            match mode {
                "check" | "repl" => {
                    command.arg(mode);
                }
                "eager" => {
                    command.arg("--eager");
                }
                _ => {}
            }
            let result = command.arg(fixture.0.join("main.cz")).output().unwrap();
            assert_eq!(
                result.status.success(),
                !used,
                "{mode}: {}",
                String::from_utf8_lossy(&result.stderr)
            );
            if !used && mode != "check" {
                assert_eq!(result.stdout, b"Holder {\n    value: selected,\n}\n");
            }
        }
    }
}
