//! Closure target availability preserves call-time diagnostics and argument effects.

use std::process::Command;

use brass_engine::{Codegen, Engine};
use brass_jit_llvm::{LlvmCodegen, OrcContext};
use brass_mir::{ClosureId, MirStmt, Rvalue};

const CHILD: &str = "BRASS_TEST_CLOSURE_TARGET";
const DIAGNOSTIC: &[u8] =
    b"runtime error: internal error: call of a closure that has no compiled instance\n";

fn source(case: &str) -> String {
    match case {
        "uncalled" => "fun main() { let f = (x: int32) -> x\n println(\"created\") }".into(),
        "void" => "fun main() { let f = () -> { println(\"body\") }\n f() }".into(),
        "named" => "fun step(x: int32) -> int32 { return x + 1 }\n\
                    fun main() { let f = step\n f(7) }"
            .into(),
        "worker" => "fun main() { let f = (x: int32) -> x\n\
                     spawn(() -> { f(7) })\n sync() }"
            .into(),
        "many" => "fun main() { let f = (x: int32, y: float64, z: string) -> z\n\
                   f(1, 2.5, \"hello\") }"
            .into(),
        ty => {
            let literal = match ty {
                "bool" => "true",
                "string" => "\"hello\"",
                "float32" | "float64" => "2.5",
                _ => "7",
            };
            format!(
                "fun effect() -> {ty} {{ println(\"argument\")\n return {literal} }}\n\
                 fun main() {{ let f = (x: {ty}) -> x\n f(effect())\n println(\"after\") }}"
            )
        }
    }
}

#[test]
fn closure_target_child() {
    let Ok(case) = std::env::var(CHILD) else {
        return;
    };
    let ast = brass_parser::parse(&source(&case)).expect("parse fixture");
    let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "{errors:?}");
    let mir = brass_mir::lower_program(&program);
    let mut mono = brass_engine::monomorphize(&mir, &program).expect("monomorphize fixture");
    let main_index = mono
        .functions
        .iter()
        .position(|f| f.symbol == "main")
        .unwrap();
    let mut body = mono.functions[main_index].body.clone();
    // Substitute only the first creation's identity, retaining its checked ABI,
    // captures and calls. Other closures, including the spawned body, stay valid.
    let mut changed = false;
    for block in &mut body.blocks {
        for stmt in &mut block.stmts {
            if !changed && let MirStmt::Assign(_, Rvalue::Closure { id, .. }) = stmt {
                *id = ClosureId(u32::MAX);
                changed = true;
            }
        }
    }
    assert!(changed, "fixture must create a closure");
    mono.functions[main_index].body = &body;
    if std::env::var_os("BRASS_TEST_CLOSURE_CACHE").is_some() {
        brass_utils::init_tracing();
    } else {
        brass_jit_llvm::disable_jit_cache();
    }
    let context = OrcContext::new();
    let mut backend = LlvmCodegen::new_orc_backend(&context, &program);
    if std::env::var_os("BRASS_TEST_WHOLE_MODULE").is_some() {
        Engine::run(&mut backend, &mono).expect("whole-module execution");
    } else if std::env::var_os("BRASS_TEST_RUNTIME_BATCH").is_some() {
        backend.begin_program(&mono);
        backend.finalize().expect("runtime support");
        backend.register_batch(&mono).expect("runtime group");
        backend.execute().expect("runtime execution");
    } else {
        backend.prepare_lazy_orc(&mono).expect("lazy preparation");
        backend.execute().expect("lazy execution");
    }
    std::process::exit(0);
}

#[test]
fn missing_targets_diagnose_only_when_called_with_their_typed_abi() {
    // Subprocesses keep the runtime's exit(1) contract observable and isolate
    // LLVM/runtime globals. Both module paths must preserve exactly this error.
    for whole_module in [false, true] {
        for case in [
            "void", "named", "worker", "many", "bool", "int8", "uint8", "int16", "uint16", "int32",
            "uint32", "int64", "uint64", "float32", "float64", "string", "int32?",
        ] {
            let mut command = Command::new(std::env::current_exe().unwrap());
            command
                .args(["--exact", "closure_target_child", "--nocapture"])
                .env(CHILD, case)
                .env("BRASS_JIT_CACHE", "off")
                .env_remove("BRASS_TEST_WHOLE_MODULE");
            if whole_module {
                command.env("BRASS_TEST_WHOLE_MODULE", "1");
            }
            let output = command.output().expect("run target fixture");
            assert_eq!(output.status.code(), Some(1), "{case}: {output:?}");
            assert_eq!(output.stderr, DIAGNOSTIC, "{case}: {output:?}");
            if !matches!(case, "void" | "named" | "worker" | "many") {
                assert!(output.stdout.ends_with(b"argument\n"), "{case}: {output:?}");
            }
        }
        let mut command = Command::new(std::env::current_exe().unwrap());
        command
            .args(["--exact", "closure_target_child", "--nocapture"])
            .env(CHILD, "uncalled")
            .env_remove("BRASS_TEST_WHOLE_MODULE");
        if whole_module {
            command.env("BRASS_TEST_WHOLE_MODULE", "1");
        }
        let output = command.output().expect("run uncalled fixture");
        assert!(output.status.success(), "{output:?}");
        assert!(output.stderr.is_empty(), "{output:?}");
        assert!(output.stdout.ends_with(b"created\n"), "{output:?}");
    }
}

#[test]
fn runtime_batch_uses_the_same_missing_target_diagnostic() {
    // Runtime-generated groups import their diagnostic helper before entry.
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "closure_target_child", "--nocapture"])
        .env(CHILD, "int32")
        .env("BRASS_TEST_RUNTIME_BATCH", "1")
        .env_remove("BRASS_TEST_WHOLE_MODULE")
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(output.stderr, DIAGNOSTIC, "{output:?}");
    assert!(output.stdout.ends_with(b"argument\n"), "{output:?}");
}

#[test]
fn missing_target_helpers_survive_cold_and_warm_object_caches() {
    // Repeated child runs exercise native helper relocation through the same cache.
    let directory =
        std::env::temp_dir().join(format!("brass-closure-cache-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    for tier in ["0", "2"] {
        let cache = directory.join(tier);
        for warm in [false, true] {
            let output = Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "closure_target_child", "--nocapture"])
                .env(CHILD, "int32")
                .env("BRASS_TEST_CLOSURE_CACHE", "1")
                .env("BRASS_JIT_CACHE", "on")
                .env("BRASS_OPT", tier)
                .env("XDG_CACHE_HOME", &cache)
                .env("BRASS_LOG", "brass::perf=debug")
                .env("NO_COLOR", "1")
                .env_remove("BRASS_TEST_WHOLE_MODULE")
                .output()
                .unwrap();
            assert_eq!(output.status.code(), Some(1), "{output:?}");
            assert!(output.stderr.ends_with(DIAGNOSTIC), "{output:?}");
            let log = String::from_utf8_lossy(&output.stderr);
            assert!(
                log.contains(if warm {
                    "jit cache hit"
                } else {
                    "jit cache store"
                }),
                "{log}"
            );
        }
    }
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn later_native_batches_reuse_missing_target_helpers() {
    let ast = brass_parser::parse(
        "fun main() { let f = (x: int32) -> x }\n\
         fun later() -> int32 { let f = (x: int32) -> x\n return 19 }",
    )
    .unwrap();
    let (program, errors) = brass_hir::lower(&[brass_hir::LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errors.is_empty(), "{errors:?}");
    let mir = brass_mir::lower_program(&program);
    let mut startup = brass_engine::monomorphize_entry(&mir, &program, false).unwrap();
    let mut later = brass_engine::monomorphize_instance_deferred(
        &mir,
        &program,
        "later",
        vec![],
        &startup.globals,
    )
    .unwrap();
    let first_index = startup
        .functions
        .iter()
        .position(|f| f.symbol == "main")
        .unwrap();
    let later_index = later
        .functions
        .iter()
        .position(|f| f.symbol == "later")
        .unwrap();
    let mut first_body = startup.functions[first_index].body.clone();
    let mut later_body = later.functions[later_index].body.clone();
    for body in [&mut first_body, &mut later_body] {
        for block in &mut body.blocks {
            for stmt in &mut block.stmts {
                if let MirStmt::Assign(_, Rvalue::Closure { id, .. }) = stmt {
                    *id = ClosureId(u32::MAX);
                }
            }
        }
    }
    startup.functions[first_index].body = &first_body;
    later.functions[later_index].body = &later_body;
    brass_jit_llvm::disable_jit_cache();
    let context = OrcContext::new();
    let mut backend = LlvmCodegen::new_orc_backend(&context, &program);
    backend.prepare_lazy_orc(&startup).unwrap();
    backend.execute().unwrap();
    // Both creators reference one ABI helper; the second module must relocate
    // against its existing definition, including when registered repeatedly.
    backend.register_batch(&later).unwrap();
    backend.register_batch(&later).unwrap();
    assert_eq!(backend.run_entry_i32("later"), Some(19));
}
