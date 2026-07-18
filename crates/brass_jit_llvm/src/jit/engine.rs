//! The JIT execution engine. Builds an LLVM
//! execution engine for the generated module, maps the runtime's C-ABI
//! primitives to their host addresses, registers each compiled function's
//! address into the runtime dispatch tables, and runs the program (module
//! initializers in order, then `main`).

use inkwell::context::Context;
use inkwell::execution_engine::ExecutionEngine;
use inkwell::module::Module;

use brass_hir::Program;
use brass_runtime::symbols;

/// Compile and run a program through the LLVM JIT.
///
/// The program is lowered to MIR and *monomorphized*, then runs through the
/// typed, fully unboxed back end (no boxed `Value`). There is no Value fallback:
/// a program whose `main` reaches a construct outside the typed subset is
/// rejected rather than executed.
#[allow(clippy::too_many_arguments)] // mirrors the checker's channel outputs
pub fn run(
    program: &Program,
    expr_types: &std::collections::HashMap<brass_hir::Span, brass_hir::Type>,
    view_args: &std::collections::HashSet<brass_hir::Span>,
    sum_views: &std::collections::HashMap<brass_hir::Span, brass_hir::Type>,
    call_locations: &std::collections::HashMap<brass_hir::Span, (String, u32, u32)>,
    lift_errs: &std::collections::HashSet<brass_hir::Span>,
    fields_loops: &std::collections::HashMap<brass_hir::Span, Vec<String>>,
    type_names: &std::collections::HashMap<brass_hir::Span, String>,
    typeof_types: &std::collections::HashMap<brass_hir::Span, brass_hir::Type>,
    null_props: &std::collections::HashSet<brass_hir::Span>,
) -> Result<(), String> {
    let mir = lower_checked(
        program,
        &brass_mir::CheckerChannels {
            expr_types,
            view_args,
            sum_views,
            call_locations,
            lift_errs,
            fields_loops,
            type_names,
            typeof_types,
            null_props,
        },
    );
    let t = std::time::Instant::now();
    let mono = brass_engine::monomorphize(&mir, program)
        .map_err(|e| format!("typed lowering failed: {e}"))?;
    tracing::debug!(
        target: "brass::perf",
        "back/monomorphize: total {:.3}ms",
        t.elapsed().as_secs_f64() * 1000.0
    );
    run_mono(program, &mono)
}

/// Compile and run an already-monomorphized program: the back half of
/// [`run`], shared with the lazy pipeline (which builds its `MonoProgram`
/// through demand-driven lowering instead of the whole-program pass).
/// Rejects a program whose `main` fell outside the typed subset, builds one
/// LLVM context/backend, and drives codegen + execution.
pub fn run_mono(program: &Program, mono: &brass_engine::MonoProgram) -> Result<(), String> {
    require_main(program, mono)?;
    let context = Context::create();
    let mut backend = crate::LlvmCodegen::new_backend(&context, program);
    brass_engine::Engine::run(&mut backend, mono)
}

/// Compile and run an already-checked program through the lazy JIT.
///
/// Module initializers and `main` are the only roots. Their statically
/// reachable call graph is compiled as one module, while unrelated
/// zero-argument functions are left out. The ordinary eager path retains its
/// all-roots validation behavior.
pub fn run_lazy(program: &Program, channels: &brass_mir::CheckerChannels) -> Result<(), String> {
    let mir = lower_checked(program, channels);
    let t = std::time::Instant::now();
    let mono =
        brass_engine::monomorphize_entry(&mir, program, false).map_err(|stop| match stop {
            brass_engine::MonoStop::MissingBodies(missing) => {
                // A full cache never leaves a reachable body unlowered, so
                // reaching this is a pipeline bug: name every demanded body
                // (with the argument types that demanded it) to make the
                // report actionable.
                let mut demands: Vec<String> = missing
                    .iter()
                    .map(|(base, args)| {
                        let args: Vec<String> = args.iter().map(|t| t.display()).collect();
                        format!("{base}({})", args.join(", "))
                    })
                    .collect();
                demands.sort();
                demands.dedup();
                format!(
                    "typed lowering failed: entry-reachable bodies are missing: {}",
                    demands.join(", ")
                )
            }
            brass_engine::MonoStop::Fail(error) => format!("typed lowering failed: {error}"),
        })?;
    tracing::debug!(
        target: "brass::perf",
        "back/monomorphize: total {:.3}ms",
        t.elapsed().as_secs_f64() * 1000.0
    );
    require_main(program, &mono)?;
    let context = crate::jit::orc::OrcContext::new();
    let mut backend = crate::LlvmCodegen::new_backend(context.context(), program);
    backend.prepare_lazy_orc(&context, &mono)?;
    backend.execute_lazy_orc()
}

fn lower_checked(
    program: &Program,
    channels: &brass_mir::CheckerChannels,
) -> brass_mir::MirProgram {
    let t = std::time::Instant::now();
    let mir = brass_mir::lower_program_with_types(
        program,
        channels.expr_types,
        channels.view_args,
        channels.sum_views,
        channels.call_locations,
        channels.lift_errs,
        channels.fields_loops,
        channels.type_names,
        channels.typeof_types,
        channels.null_props,
    );
    tracing::debug!(
        target: "brass::perf",
        "back/lower-mir: total {:.3}ms",
        t.elapsed().as_secs_f64() * 1000.0
    );
    // MIR is rendered only on request because it can dwarf ordinary logs.
    if tracing::enabled!(target: "brass::mir", tracing::Level::TRACE) {
        tracing::trace!(target: "brass::mir", "\n{}", brass_mir::program_to_string(&mir));
    }
    mir
}

fn require_main(program: &Program, mono: &brass_engine::MonoProgram) -> Result<(), String> {
    if program.functions.contains_key("main") && mono.lookup("main").is_none() {
        return Err(match &mono.main_skip {
            Some(reason) => {
                format!("program uses constructs outside the typed (Value-free) subset: {reason}")
            }
            None => "program uses constructs outside the typed (Value-free) subset".to_string(),
        });
    }
    Ok(())
}

/// Map every runtime primitive the module declares to its host address. This
/// includes the deferred-dispatch trampoline `pp_resolve`, which
/// lives in the JIT crate rather than `brass_runtime`.
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
    use brass_hir::{IntKind, Type};
    use inkwell::OptimizationLevel;
    use inkwell::context::Context;

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
