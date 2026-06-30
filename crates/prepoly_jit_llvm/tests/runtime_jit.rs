//! End-to-end test of the runtime JIT compilation backend: the
//! `prepoly_engine`-defined `RuntimeJit` trait, implemented by the LLVM backend,
//! compiles a monomorphized instance into the *live* execution engine after
//! `finalize` and returns its callable address.

use inkwell::context::Context;
use prepoly_engine::{
    Codegen, MonomorphCache, RuntimeJit, boundary_record_type, instance_symbol,
    monomorphize_instance, resolve_or_compile,
};
use prepoly_hir::{IntKind, Type};
use prepoly_jit_llvm::{LlvmCodegen, RuntimeDispatcher, with_dispatcher};

/// After the engine is finalized (instances only declared), an instance compiled
/// at runtime through `RuntimeJit::compile_instance` is callable and correct --
/// the capability deferred monomorphization is built on, exercised through the
/// clean engine-trait / jit_llvm-impl boundary.
#[test]
fn compiles_and_runs_an_instance_after_finalize() {
    let src = "fun triple(n: int32) -> int32 {\n  return n + n + n\n}\n\
               fun main() {\n  let x = triple(7)\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errs) = prepoly_hir::lower(&[prepoly_hir::LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errs.is_empty(), "lower: {errs:?}");
    let mir = prepoly_mir::lower_program(&program);
    let mono = prepoly_engine::monomorphize(&mir, &program).expect("monomorphize");

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    // Declare every instance, then finalize -- no bodies are emitted statically.
    backend.begin_program(&mono);
    backend.finalize().expect("finalize");

    // Compile `triple` at runtime and call it through the returned address.
    let f = mono
        .functions
        .iter()
        .find(|f| f.symbol.contains("triple"))
        .expect("triple instance");
    let addr = backend
        .compile_instance(&mono, f)
        .expect("runtime instance compiles");
    let triple: extern "C" fn(i32) -> i32 = unsafe { std::mem::transmute(addr) };
    assert_eq!(triple(7), 21);
}

/// On-demand monomorphization: a consumer with a *deferred*
/// parameter is specialized for a type discovered "at runtime" and compiled then.
/// `get_age(p)` was never specialized statically (its `p` is unannotated and it is
/// not called with `Person`); monomorphize_instance specializes it for `Person`,
/// and the LLVM backend compiles that instance into the live engine.
#[test]
fn on_demand_monomorphize_and_compile_for_a_runtime_type() {
    let src = "type Person = {\n  age: int32\n}\n\
               fun get_age(p) -> int32 {\n  return p.age\n}\n\
               fun main() {\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errs) = prepoly_hir::lower(&[prepoly_hir::LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errs.is_empty(), "lower: {errs:?}");
    let mir = prepoly_mir::lower_program(&program);

    // The type fixed "at runtime" (as the deserialize boundary would build it):
    // a record nominal carrying its field types, exactly as a constructed record.
    let person = prepoly_engine::boundary_record_type(&program, &["main".into()], "Person")
        .expect("Person record type");
    let get_age = mir
        .functions
        .iter()
        .find(|f| f.name == "get_age")
        .map(|f| f.symbol.clone())
        .expect("get_age lowered");

    // Specialize `get_age` for `p: Person` on demand. A type missing `age` would
    // make this fail -- the structural check enforced at the boundary.
    let mono =
        prepoly_engine::monomorphize_instance(&mir, &program, &get_age, vec![person.clone()])
            .expect("on-demand monomorphization");
    let inst = prepoly_engine::instance_symbol(&get_age, std::slice::from_ref(&person));
    let f = mono.lookup(&inst).expect("the specialized instance");
    assert_eq!(
        f.type_args,
        vec![person.clone()],
        "p is specialized to Person"
    );
    assert_eq!(f.ret, Type::Int(IntKind::I32), "p.age is int32");

    // Compile the on-demand instance into a live engine.
    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    backend.begin_program(&mono);
    backend.finalize().expect("finalize");
    let addr = backend
        .compile_instance(&mono, f)
        .expect("on-demand instance compiles");
    assert!(addr != 0, "compiled instance has an address");
}

/// The full deferred-monomorphization flow: a consumer of an externally-typed
/// value is compiled once per
/// distinct runtime type (cached) and runs correctly on a value of that type;
/// a runtime type missing a required field is rejected at the boundary rather
/// than miscompiled. Driven here through the engine's `resolve_or_compile`
/// orchestration over the LLVM `RuntimeJit` backend.
#[test]
fn deferred_monomorphization_end_to_end() {
    let src = "type Person = {\n  age: int32\n}\n\
               type Other = {\n  name: string\n}\n\
               fun get_age(p) -> int32 {\n  return p.age\n}\n\
               fun main() {\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errs) = prepoly_hir::lower(&[prepoly_hir::LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errs.is_empty(), "lower: {errs:?}");
    let mir = prepoly_mir::lower_program(&program);

    let person = boundary_record_type(&program, &["main".into()], "Person").expect("Person type");
    let get_age = mir
        .functions
        .iter()
        .find(|f| f.name == "get_age")
        .map(|f| f.symbol.clone())
        .expect("get_age");
    let mono = monomorphize_instance(&mir, &program, &get_age, vec![person.clone()])
        .expect("specialize get_age for Person");
    let inst = instance_symbol(&get_age, &[person]);

    let ctx = Context::create();
    let mut backend = LlvmCodegen::new_backend(&ctx, &program);
    backend.begin_program(&mono);
    backend.finalize().expect("finalize");

    // Compile-once-per-type, cached: two requests for the same instance compile
    // it once and return the same address.
    let mut cache = MonomorphCache::new();
    let addr1 = resolve_or_compile(&mut cache, &mut backend, &mono, &inst).expect("resolve");
    let addr2 = resolve_or_compile(&mut cache, &mut backend, &mono, &inst).expect("cached");
    assert_eq!(addr1, addr2);
    assert_eq!(cache.len(), 1, "compiled once, then cached");

    // Dispatch: build a `Person { age: 42 }` (header16 | age@16) as the boundary
    // value and call the on-demand-compiled consumer on it.
    let mut storage = [0u64; 3];
    storage[2] = 42; // int32 `age` at byte offset 16
    let person_ptr = storage.as_mut_ptr() as *mut std::ffi::c_void;
    let get_age_fn: extern "C" fn(*mut std::ffi::c_void) -> i32 =
        unsafe { std::mem::transmute(addr1) };
    assert_eq!(
        get_age_fn(person_ptr),
        42,
        "deferred dispatch returns p.age"
    );

    // A runtime type missing `age` is rejected before specialization.
    let other = boundary_record_type(&program, &["main".into()], "Other").expect("Other type");
    assert!(
        monomorphize_instance(&mir, &program, &get_age, vec![other]).is_err(),
        "a type missing `age` must be rejected at the boundary, not miscompiled"
    );
}

/// The in-language end-to-end: a Prepoly program whose `run_it`
/// calls the `__rt_dispatch` builtin triggers deferred monomorphization at
/// runtime -- `get_age` is JIT-compiled for `Person` in the dispatcher's engine
/// (separate from the engine running the program, so compiling never reentrantly
/// mutates it) and dispatched on the value, returning `p.age`.
#[test]
fn prepoly_program_triggers_deferred_dispatch() {
    let src = "type Person = {\n  age: int32\n}\n\
               fun get_age(p) -> int32 {\n  return p.age\n}\n\
               fun run_it(p: Person) -> int32 {\n  return __rt_dispatch(\"get_age\", \"Person\", p)\n}\n\
               fun main() {\n  let seed = Person { age: 0 }\n  let _ = run_it(seed)\n}\n";
    let ast = prepoly_parser::parse(src).expect("parse");
    let (program, errs) = prepoly_hir::lower(&[prepoly_hir::LoadedModule {
        path: vec!["main".into()],
        ast,
    }]);
    assert!(errs.is_empty(), "lower: {errs:?}");
    let mir = prepoly_mir::lower_program(&program);
    let static_mono = prepoly_engine::monomorphize(&mir, &program).expect("monomorphize");

    let person = boundary_record_type(&program, &["main".into()], "Person").expect("Person type");
    let run_it = mir
        .functions
        .iter()
        .find(|f| f.name == "run_it")
        .map(|f| f.symbol.clone())
        .expect("run_it");
    let run_it_inst = instance_symbol(&run_it, &[person]);

    let ctx = Context::create();
    // The engine that runs the program (compiles `run_it`, whose body calls
    // `__rt_dispatch` -> `pp_resolve`).
    let mut main_backend = LlvmCodegen::new_backend(&ctx, &program);
    main_backend.begin_program(&static_mono);
    main_backend.codegen_program(&static_mono);
    main_backend.finalize().expect("finalize main");

    // A *separate* engine for the dispatcher, so compiling a deferred instance
    // never reentrantly mutates the engine running the program.
    let mut disp_backend = LlvmCodegen::new_backend(&ctx, &program);
    disp_backend.begin_program(&static_mono);
    disp_backend.finalize().expect("finalize dispatcher");

    let run_it_addr = main_backend
        .address_of(&run_it_inst)
        .expect("run_it$Person compiled");
    // A `Person { age: 42 }` value (header16 | age@16).
    let mut storage = [0u64; 3];
    storage[2] = 42;
    let person_ptr = storage.as_mut_ptr() as *mut std::ffi::c_void;
    let run_it_fn: extern "C" fn(*mut std::ffi::c_void) -> i32 =
        unsafe { std::mem::transmute(run_it_addr) };

    let mut dispatcher = RuntimeDispatcher::new(&mir, &program, &mut disp_backend);
    let result = with_dispatcher(&mut dispatcher, || run_it_fn(person_ptr));
    assert_eq!(
        result, 42,
        "a Prepoly program triggered deferred compilation + dispatch of get_age"
    );
}
