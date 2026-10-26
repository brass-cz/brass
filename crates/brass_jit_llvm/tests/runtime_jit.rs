//! Runtime compilation into a live engine: after `finalize`, the lazy JIT's
//! resolver registers monomorphized batches with `LlvmCodegen::register_batch`
//! and looks their bodies up with `address_of`. These tests drive that API
//! directly, without the driver.

use brass_engine::Codegen;
use inkwell::context::Context;

/// Parse a single-module program and lower it to HIR and MIR.
fn lower(src: &str) -> (brass_hir::Program, brass_mir::MirProgram) {
    let ast = brass_parser::parse(src).expect("parse");
    let (program, errs) = brass_hir::lower(&[brass_hir::LoadedModule {
        is_prelude: false,
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errs.is_empty(), "lower: {errs:?}");
    let mir = brass_mir::lower_program(&program);
    (program, mir)
}

/// After the engine is finalized with every instance only declared, a batch
/// registered at runtime is callable and computes the right value.
#[test]
fn compiles_and_runs_an_instance_after_finalize() {
    let (program, mir) = lower(
        "fun triple(n: int32) -> int32 {\n  return n + n + n\n}\n\
         fun main() {\n  let x = triple(7)\n}\n",
    );
    let mono = brass_engine::monomorphize(&mir, &program).expect("monomorphize");

    brass_jit_llvm::disable_jit_cache();
    let ctx = Context::create();
    let mut backend = brass_jit_llvm::LlvmCodegen::new_backend(&ctx, &program);
    // Declare every instance, then finalize -- no bodies are emitted statically.
    backend.begin_program(&mono);
    backend.finalize().expect("finalize");

    let symbol = &mono
        .functions
        .iter()
        .find(|f| f.symbol.contains("triple"))
        .expect("triple instance")
        .symbol;
    backend.register_batch(&mono).expect("runtime batch");
    let addr = backend
        .address_of(symbol)
        .expect("runtime instance compiles");
    let triple: extern "C" fn(i32) -> i32 = unsafe { std::mem::transmute(addr) };
    assert_eq!(triple(7), 21);
}

/// A runtime batch includes the requested instance's new callees, skips a
/// definition supplied at startup, and can be registered twice without
/// redefining symbols or changing addresses.
#[test]
fn runtime_batch_keeps_startup_definitions_and_registers_callees() {
    let (program, mir) = lower(
        "fun seed() -> int32 { return 10 }\n\
         fun helper() -> int32 { return 7 }\n\
         fun answer() -> int32 { return seed() + helper() }\n\
         fun main() { let value = answer() }\n",
    );
    let mono = brass_engine::monomorphize(&mir, &program).expect("monomorphize");
    brass_jit_llvm::disable_jit_cache();
    let ctx = Context::create();
    let mut backend = brass_jit_llvm::LlvmCodegen::new_backend(&ctx, &program);
    backend.begin_program(&mono);
    let seed = mono
        .functions
        .iter()
        .find(|f| f.symbol == "seed")
        .expect("seed");
    backend.codegen_function(&mono, seed);
    backend.finalize().expect("finalize startup");
    let seed_address = backend.address_of(&seed.symbol).expect("startup address");

    backend.register_batch(&mono).expect("register batch");
    let first = backend.address_of("answer").expect("answer address");
    backend.register_batch(&mono).expect("repeat batch");
    let second = backend.address_of("answer").expect("answer address");
    assert_eq!(first, second);
    assert_eq!(backend.address_of(&seed.symbol), Some(seed_address));
    assert_eq!(backend.run_entry_i32("answer"), Some(17));
}
