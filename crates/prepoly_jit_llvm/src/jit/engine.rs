//! The JIT execution engine. Builds an LLVM
//! execution engine for the generated module, maps the runtime's C-ABI
//! primitives to their host addresses, registers each compiled function's
//! address into the runtime dispatch tables, and runs the program (module
//! initializers in order, then `main`).

use inkwell::context::Context;
use inkwell::execution_engine::ExecutionEngine;
use inkwell::module::Module;

use prepoly_hir::Program;
use prepoly_runtime::symbols;

/// Compile and run a program through the LLVM JIT.
///
/// The program is lowered to MIR and *monomorphized*, then runs through the
/// typed, fully unboxed back end (no boxed `Value`). There is no Value fallback:
/// a program whose `main` reaches a construct outside the typed subset is
/// rejected rather than executed.
#[allow(clippy::too_many_arguments)] // mirrors the checker's channel outputs
pub fn run(
    program: &Program,
    _int_lit_types: &std::collections::HashMap<prepoly_hir::Span, prepoly_hir::IntKind>,
    expr_types: &std::collections::HashMap<prepoly_hir::Span, prepoly_hir::Type>,
    view_args: &std::collections::HashSet<prepoly_hir::Span>,
    fields_loops: &std::collections::HashMap<prepoly_hir::Span, Vec<String>>,
    type_names: &std::collections::HashMap<prepoly_hir::Span, String>,
    typeof_types: &std::collections::HashMap<prepoly_hir::Span, prepoly_hir::Type>,
    null_props: &std::collections::HashSet<prepoly_hir::Span>,
) -> Result<(), String> {
    let mir = prepoly_mir::lower_program_with_types(
        program,
        expr_types,
        view_args,
        fields_loops,
        type_names,
        typeof_types,
        null_props,
    );
    // Debugging aid: dump the lowered MIR when requested
    // (PREPOLY_LOG_TYPE=mir) -- the first thing needed when monomorphization
    // rejects a checked program. Guarded so the rendering only runs when the
    // target is enabled.
    if tracing::enabled!(target: "prepoly::mir", tracing::Level::TRACE) {
        tracing::trace!(target: "prepoly::mir", "\n{}", prepoly_mir::program_to_string(&mir));
    }
    let mono = prepoly_engine::monomorphize(&mir, program)
        .map_err(|e| format!("typed lowering failed: {e}"))?;
    // No Value fallback: a program outside the typed subset is rejected. The
    // skip reason names the first offending construct -- without it the user
    // sees only the generic sentence for a program the checker accepted.
    if program.functions.contains_key("main") && mono.lookup("main").is_none() {
        return Err(match &mono.main_skip {
            Some(reason) => {
                format!("program uses constructs outside the typed (Value-free) subset: {reason}")
            }
            None => "program uses constructs outside the typed (Value-free) subset".to_string(),
        });
    }
    let context = Context::create();
    let mut backend = crate::LlvmCodegen::new_backend(&context, program);
    prepoly_engine::Engine::run(&mut backend, &mono)
}

/// Map every runtime primitive the module declares to its host address. This
/// includes the deferred-dispatch trampoline `pp_resolve`, which
/// lives in the JIT crate rather than `prepoly_runtime`.
pub(crate) fn map_runtime_symbols(engine: &ExecutionEngine, module: &Module) {
    for (name, addr) in symbols() {
        if let Some(f) = module.get_function(name) {
            engine.add_global_mapping(&f, addr);
        }
    }
    if let Some(f) = module.get_function("pp_resolve") {
        engine.add_global_mapping(&f, crate::dispatch::pp_resolve as *const () as usize);
    }
}

#[cfg(test)]
mod tests {
    use crate::layout::Abi;
    use inkwell::OptimizationLevel;
    use inkwell::context::Context;
    use prepoly_hir::{IntKind, Type};

    /// A typed `int32 -> int32` callable lowered with
    /// the unboxed signature `i32 (i32, i32)` JIT-compiles and executes. This
    /// exercises the typed backend's layout/signature path end to end, distinct
    /// from the uniform tagged-value ABI.
    #[test]
    fn typed_int32_function_jits_and_runs() {
        let ctx = Context::create();
        let module = ctx.create_module("typed_add");
        let abi = Abi::new(&ctx);
        let i32t = Type::Int(IntKind::I32);

        let fty = abi.typed_fn_type(&[i32t.clone(), i32t.clone()], &i32t);
        let f = module.add_function("add_i32", fty, None);
        let builder = ctx.create_builder();
        let entry = ctx.append_basic_block(f, "entry");
        builder.position_at_end(entry);
        let a = f.get_nth_param(0).unwrap().into_int_value();
        let b = f.get_nth_param(1).unwrap().into_int_value();
        let sum = builder.build_int_add(a, b, "sum").unwrap();
        builder.build_return(Some(&sum)).unwrap();

        let engine = module
            .create_jit_execution_engine(OptimizationLevel::None)
            .expect("jit engine");
        type AddFn = unsafe extern "C" fn(i32, i32) -> i32;
        let add = unsafe {
            engine
                .get_function::<AddFn>("add_i32")
                .expect("typed function address")
        };
        assert_eq!(unsafe { add.call(2, 3) }, 5);
        assert_eq!(unsafe { add.call(-1, 41) }, 40);
    }

    /// Deferred monomorphization requires JIT-compiling new code
    /// *after* the engine is built, when a runtime type first arrives. This proves
    /// the engine can take a module added later (in the same context) and execute
    /// its function -- the capability the compiler-as-runtime-service is built on.
    #[test]
    fn engine_runs_a_module_added_after_startup() {
        let ctx = Context::create();
        let abi = Abi::new(&ctx);
        let i32t = Type::Int(IntKind::I32);

        // Startup module + engine (as a real run would have).
        let m1 = ctx.create_module("startup");
        let f1 = m1.add_function(
            "seed",
            abi.typed_fn_type(std::slice::from_ref(&i32t), &i32t),
            None,
        );
        let b = ctx.create_builder();
        b.position_at_end(ctx.append_basic_block(f1, "e"));
        b.build_return(Some(&f1.get_nth_param(0).unwrap())).unwrap();
        let engine = m1
            .create_jit_execution_engine(OptimizationLevel::None)
            .expect("jit engine");

        // A second module compiled "at runtime" and added to the live engine.
        let m2 = ctx.create_module("deferred");
        let f2 = m2.add_function(
            "triple",
            abi.typed_fn_type(std::slice::from_ref(&i32t), &i32t),
            None,
        );
        let b2 = ctx.create_builder();
        b2.position_at_end(ctx.append_basic_block(f2, "e"));
        let x = f2.get_nth_param(0).unwrap().into_int_value();
        let three = ctx.i32_type().const_int(3, false);
        let r = b2.build_int_mul(x, three, "r").unwrap();
        b2.build_return(Some(&r)).unwrap();
        engine.add_module(&m2).expect("add a runtime module");

        type IntFn = unsafe extern "C" fn(i32) -> i32;
        let triple = unsafe { engine.get_function::<IntFn>("triple") }.expect("runtime fn address");
        assert_eq!(unsafe { triple.call(7) }, 21);
    }
}
