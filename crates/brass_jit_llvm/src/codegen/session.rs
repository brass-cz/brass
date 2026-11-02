//! Module finalization and the ORC session: the whole-module optimization
//! pipeline, the post-init freeze of immutable heap globals, lazy function
//! groups and their batch-shared helper modules, entry execution, and
//! lookups of compiled instances.

use fxhash::FxHashMap as HashMap;
use std::cell::RefCell;
use std::rc::Rc;

use inkwell::OptimizationLevel;
use inkwell::types::FunctionType;
use inkwell::values::FunctionValue;

use brass_engine::{Codegen as EngineCodegen, MonoFunction, MonoProgram};
use brass_hir::Type;

use crate::jit::orc::{OptTier, OrcContext, OrcJit, OrcModule, lazy_implementation_symbol};
use crate::monomorph::mangle_fn;

use super::{LlvmCodegen, unwrap_copy_wrappers};

/// The generated function that auto-freezes immutable heap globals after module
/// init; the entry sequence calls it between the inits and `main`.
const FREEZE_GLOBALS_FN: &str = "__pp_freeze_globals";

/// The module globals that are immutable (never reassigned outside their
/// initializer) and heap-pointer-typed -- the ones auto-frozen after init. A
/// global written by any non-initializer instance is mutable and left
/// thread-local (the auto-cown candidates).
pub(super) fn immutable_heap_globals(program: &MonoProgram) -> Vec<String> {
    use fxhash::FxHashSet as HashSet;
    let inits: HashSet<&str> = program.init_symbols.iter().map(|s| s.as_str()).collect();
    let mut mutated: HashSet<&str> = HashSet::default();
    for f in &program.functions {
        if inits.contains(f.symbol.as_str()) {
            continue;
        }
        for block in &f.body.blocks {
            for stmt in &block.stmts {
                if let brass_mir::MirStmt::SetGlobal(name, _) = stmt {
                    mutated.insert(name.as_str());
                }
            }
        }
    }
    program
        .globals
        .iter()
        .filter(|(name, ty)| is_heap_pointer_type(ty) && !mutated.contains(name.as_str()))
        .map(|(name, _)| name.clone())
        .collect()
}

/// Whether a global's runtime representation is a managed heap pointer that the
/// freeze entry can read from its slot. Passing-mode wrappers preserve that
/// representation.
fn is_heap_pointer_type(ty: &Type) -> bool {
    matches!(
        unwrap_copy_wrappers(ty),
        Type::Str
            | Type::Record(..)
            | Type::Sum(..)
            | Type::Slice(..)
            | Type::Array(..)
            | Type::Fun(..)
            | Type::Tuple(..)
            | Type::Nullable(..)
    )
}

/// The module-level global symbol for a program global of the given name.
fn mangle_global(n: &str) -> String {
    format!(
        "pp_g_{}",
        n.chars()
            .map(|c| if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            })
            .collect::<String>()
    )
}

fn group_size_for(tier: OptTier) -> usize {
    match tier {
        OptTier::O0 => 16,
        OptTier::O2 => 16,
    }
}

impl<'ctx, 'p> LlvmCodegen<'ctx, 'p> {
    /// Declare each typed global; with `define`, zero-initialized (init
    /// instances fill them). A lazy group module only DECLARES them (no
    /// initializer): the linker then resolves the reference to the defining
    /// module's storage (the whole module, or a lazy run's support module),
    /// where the program's actual state lives.
    pub(super) fn declare_globals(&mut self, program: &MonoProgram, define: bool) {
        for (name, ty) in &program.globals {
            let llty = self.abi.typed_basic(ty);
            let g = self.module.add_global(llty, None, &mangle_global(name));
            if define {
                g.set_initializer(&llty.const_zero());
            }
            self.mir.globals.insert(name.clone(), g);
        }
    }

    /// The module-local declaration of a monomorphized instance, or `None`
    /// when no such instance exists. Whole-module callers pre-declare every
    /// instance in `begin_program`; startup and runtime lazy groups declare
    /// an instance the first time a body references it, from the shared
    /// per-program signature table.
    pub(super) fn instance_fn(&mut self, symbol: &str) -> Option<FunctionValue<'ctx>> {
        let name = mangle_fn(symbol);
        if let Some(f) = self.fns.map.get(&name) {
            return Some(*f);
        }
        let fty = *self.mir.lazy_signatures.as_ref()?.get(&name)?;
        let f = self.module.add_function(&name, fty, None);
        self.fns.map.insert(name, f);
        Some(f)
    }

    /// Prepare a lazy run as independent, unoptimized function modules.
    /// ORC receives a callable stub for every monomorphized instance; its
    /// tier-selected transform and native code generator do no work for a
    /// module until that stub is entered by executed control flow.
    pub fn prepare_lazy_orc(&mut self, program: &MonoProgram) -> Result<(), String> {
        self.create_orc(OptTier::from_env())?;
        self.register_batch(program)?;
        self.mir.lazy_precompile = brass_engine::spawn_precompile(program).unwrap_or_default();
        // The support module owns globals and the freeze entry; declarations
        // for functions are unnecessary until a body actually references them.
        self.declare_globals(program, true);
        self.mir.init_symbols = program.init_symbols.clone();
        self.mir.frozen_globals = immutable_heap_globals(program);
        self.mir.entry_symbol = program.entry_function().map(|f| f.symbol.clone());
        self.emit_freeze_globals_fn();
        self.module
            .verify()
            .map_err(|e| format!("LLVM support module verification failed:\n{e}"))?;
        let jit = self.mir.orc.as_ref().expect("ORC session created");
        let module = std::mem::replace(&mut self.module, self.ctx.create_module("brass"));
        jit.add_eager_module(jit.own_module(module)?)
    }

    /// Start this backend's ORC session at `tier`, with the runtime's C-ABI
    /// primitives and the deferred-call trampoline `pp_resolve` defined at
    /// their host addresses. A backend has at most one session.
    pub(super) fn create_orc(&mut self, tier: OptTier) -> Result<(), String> {
        if self.mir.orc.is_some() {
            return Err("JIT backend was finalized twice".into());
        }
        let fallback = self.orc_context.is_none().then(OrcContext::new);
        let context = self.orc_context.or(fallback.as_ref()).expect("ORC context");
        let jit = OrcJit::with_cache(context, crate::jit::objcache::ObjectStore::from_env(), tier)?;
        jit.define_absolute(
            brass_runtime::symbols()
                .into_iter()
                .map(|(name, address)| (name.to_string(), address))
                .chain(std::iter::once((
                    "pp_resolve".into(),
                    crate::dispatch::pp_resolve as *const () as usize,
                ))),
        )?;
        self.mir.orc = Some(jit);
        Ok(())
    }

    /// Emit and register every new body before looking up any implementation.
    /// Signatures are shared, but each module declares only referenced callees.
    /// Stable input order and module names make identical batches cacheable;
    /// already defined startup or runtime instances are never defined twice.
    pub fn register_batch(&mut self, program: &MonoProgram) -> Result<(), String> {
        let jit = self
            .mir
            .orc
            .as_ref()
            .ok_or("register_batch called before ORC preparation")?;
        let signatures: std::rc::Rc<HashMap<String, FunctionType<'ctx>>> = std::rc::Rc::new(
            program
                .functions
                .iter()
                .map(|f| {
                    let ty = if f.is_closure {
                        self.abi.typed_closure_fn_type(&f.type_args, &f.ret)
                    } else {
                        self.abi.typed_fn_type(&f.type_args, &f.ret)
                    };
                    (mangle_fn(&f.symbol), ty)
                })
                .collect(),
        );
        let functions: Vec<_> = program
            .functions
            .iter()
            .filter(|f| !self.has_instance(&f.symbol))
            .collect();
        // Small programs preserve first-use granularity. Wider batches group
        // nearby discoveries to amortize LLVM pipeline and linking overhead.
        let size = if functions.len() > 32 {
            group_size_for(jit.tier())
        } else {
            1
        };
        let region_barriers = brass_engine::program_uses_with(program);
        let mut helper_codegen = Self::new_backend(self.ctx, self.program);
        helper_codegen.previous_helpers = Some(self.mir.helpers.clone());
        helper_codegen.region_barriers = region_barriers;
        helper_codegen.mir.lazy_signatures = Some(signatures.clone());
        // The first new instance fixes this batch's identity independently of
        // hash-map order or which group ORC happens to materialize first.
        let helper_name = format!(
            "brass.helpers.{}",
            functions.first().map_or("empty", |f| &f.symbol)
        );
        helper_codegen.module.set_name(&helper_name);
        helper_codegen.module.set_source_file_name(&helper_name);
        let helpers = Rc::new(RefCell::new(helper_codegen));
        let mut perf = brass_utils::PerfLog::start("back/codegen-fn");
        let mut groups = Vec::new();
        for chunk in functions.chunks(size) {
            let publics: Vec<_> = chunk.iter().map(|f| mangle_fn(&f.symbol)).collect();
            let module = self.lazy_group_module(
                program,
                chunk,
                signatures.clone(),
                region_barriers,
                helpers.clone(),
                &mut perf,
            )?;
            groups.push((publics, module));
        }
        perf.report();
        let helper_codegen = Rc::try_unwrap(helpers)
            .ok()
            .expect("batch helper owner")
            .into_inner();
        let helper_symbols: Vec<_> = helper_codegen
            .module
            .get_functions()
            .filter(|f| f.count_basic_blocks() != 0)
            .map(|f| f.get_name().to_string_lossy().into_owned())
            .collect();
        if !helper_symbols.is_empty() {
            helper_codegen
                .module
                .verify()
                .map_err(|e| format!("helper module verification failed:\n{e}"))?;
            helper_codegen.mark_small_functions_alwaysinline();
            if tracing::enabled!(target: "brass::ir", tracing::Level::TRACE) {
                tracing::trace!(target: "brass::ir", "\n{}", helper_codegen.module.print_to_string().to_string());
            }
            jit.add_helpers(&helper_symbols, jit.own_module(helper_codegen.module)?)?;
            Rc::make_mut(&mut self.mir.helpers).extend(helper_symbols);
        }
        for (publics, module) in groups {
            jit.add_lazy_group(&publics, module)?;
            self.mir
                .defined
                .extend(publics.into_iter().map(|symbol| (symbol, true)));
        }
        Ok(())
    }

    /// Materialize every instance a spawned worker may enter (the startup
    /// program's spawn-reachable set) before entering JIT code, and prime
    /// the cross-thread resolved-address cache with their addresses: workers
    /// cannot run the compiler, so their deferred calls must find every
    /// target already resolved.
    pub fn precompile_spawn(&self) -> Result<(), String> {
        for symbol in &self.mir.lazy_precompile {
            let address = self
                .address_of(symbol)
                .ok_or_else(|| format!("worker body `{symbol}` is unavailable"))?;
            crate::dispatch::prime_resolved(symbol, address);
        }
        Ok(())
    }

    /// Materialize every body registered in this session, for a runtime batch
    /// that spawns: its deferred targets can call previously registered bodies
    /// outside the batch, so all of them are compiled before workers start.
    pub fn materialize_all(&self) -> Result<(), String> {
        let jit = self.mir.orc.as_ref().ok_or("missing ORC session")?;
        let mut symbols: Vec<_> = self.mir.defined.iter().collect();
        symbols.sort_by_key(|(symbol, _)| *symbol);
        for (symbol, lazy) in symbols {
            jit.lookup(&if *lazy {
                lazy_implementation_symbol(symbol)
            } else {
                symbol.clone()
            })?;
        }
        Ok(())
    }

    fn entry_addresses(&self) -> Result<Vec<usize>, String> {
        self.precompile_spawn()?;
        let jit = self
            .mir
            .orc
            .as_ref()
            .ok_or("execute called before finalize")?;
        let mut symbols: Vec<_> = self.mir.init_symbols.iter().map(|s| mangle_fn(s)).collect();
        if !self.mir.frozen_globals.is_empty() {
            symbols.push(FREEZE_GLOBALS_FN.into());
        }
        if let Some(entry) = &self.mir.entry_symbol {
            symbols.push(mangle_fn(entry));
        }
        symbols.iter().map(|s| jit.lookup(s)).collect()
    }

    /// Execute init, freeze, and main with the runtime resolver installed, then
    /// join spawned tasks, run a final collection and report session errors.
    /// All entry lookups finish first. During native calls only dispatch.rs's
    /// scoped raw pointer can borrow the compiler; ORC callbacks use
    /// independent state.
    pub fn execute_with_resolver(
        &mut self,
        resolve: &mut dyn FnMut(&mut LlvmCodegen<'ctx, 'p>, &str) -> usize,
    ) -> Result<(), String> {
        let addresses = self.entry_addresses()?;
        crate::dispatch::with_deferred_resolver(self, resolve, || {
            for address in addresses {
                crate::dispatch::call_void(address);
            }
            brass_runtime::conc::pp_join_all();
        });
        crate::dispatch::clear_resolved();
        brass_runtime::gc::pp_gc_collect();
        self.mir
            .orc
            .as_ref()
            .expect("live ORC session")
            .check_reported_errors()
    }

    /// [`Self::execute_with_resolver`] without a resolver, for a program whose
    /// every instance was registered before the run (no deferred call can
    /// reach a body the session lacks).
    pub(crate) fn execute_lazy_orc(&mut self) -> Result<(), String> {
        let _resolved_session = crate::dispatch::resolved_session();
        let materialize = std::time::Instant::now();
        let addresses = self.entry_addresses()?;
        brass_utils::perf_phase("back/eager-entry-addresses", materialize.elapsed());
        // Native exit does not return through these completion markers.
        tracing::debug!(target: "brass::perf", "back/eager-execute: start");
        let execute = std::time::Instant::now();
        for address in addresses {
            crate::dispatch::call_void(address);
        }
        brass_runtime::conc::pp_join_all();
        brass_utils::perf_phase("back/eager-execute", execute.elapsed());
        let cleanup = std::time::Instant::now();
        brass_runtime::gc::pp_gc_collect();
        let result = self
            .mir
            .orc
            .as_ref()
            .expect("live ORC session")
            .check_reported_errors();
        brass_utils::perf_phase("back/eager-runtime-cleanup", cleanup.elapsed());
        result
    }

    /// Emit one lazy GROUP module: the bodies of `functions`, each defined
    /// under its implementation symbol. A group-mate referenced by another
    /// member resolves to the local definition directly (no stub round trip);
    /// instances outside the group stay external declarations resolved
    /// through their public stubs.
    fn lazy_group_module(
        &self,
        program: &MonoProgram,
        functions: &[&MonoFunction],
        signatures: std::rc::Rc<HashMap<String, FunctionType<'ctx>>>,
        region_barriers: bool,
        helpers: Rc<RefCell<LlvmCodegen<'ctx, 'p>>>,
        perf: &mut brass_utils::PerfLog,
    ) -> Result<OrcModule, String> {
        let mut codegen = LlvmCodegen::new_backend(self.ctx, self.program);
        // Globals belong to the support module; this one only references them.
        codegen.mir.lazy_signatures = Some(signatures);
        codegen.region_barriers = region_barriers;
        codegen.helpers = Some(helpers);
        codegen.declare_globals(program, false);
        for function in functions {
            let started = std::time::Instant::now();
            codegen.codegen_function(program, function);
            perf.item(function.symbol.clone(), started.elapsed());
        }
        // Rename after every body is emitted: a member emitted later must
        // still find the earlier definitions in the function map.
        for function in functions {
            let public = mangle_fn(&function.symbol);
            let definition = codegen
                .module
                .get_function(&public)
                .ok_or_else(|| format!("generated function `{public}` is missing"))?;
            definition
                .as_global_value()
                .set_name(&lazy_implementation_symbol(&public));
        }
        codegen.mark_small_functions_alwaysinline();
        codegen
            .module
            .verify()
            .map_err(|error| format!("lazy function verification failed:\n{error}"))?;
        if tracing::enabled!(target: "brass::ir", tracing::Level::TRACE) {
            tracing::trace!(target: "brass::ir", "\n{}", codegen.module.print_to_string().to_string());
        }
        self.mir
            .orc
            .as_ref()
            .expect("live ORC session")
            .own_module(codegen.module)
    }

    /// Mark small defined functions `alwaysinline`, respecting `noinline`. "Small" is
    /// approximated by basic-block count: a handful of blocks is a leaf-ish helper
    /// (accessors, tiny arithmetic wrappers like `std/math`'s `pow`) that is cheaper
    /// to inline than to call. Functions keep their external definition (so direct
    /// and deferred calls still resolve); only call sites are inlined.
    pub(super) fn mark_small_functions_alwaysinline(&self) {
        const SMALL_BLOCKS: u32 = 4;
        let kind = inkwell::attributes::Attribute::get_named_enum_kind_id("alwaysinline");
        if kind == 0 {
            return;
        }
        let noinline = inkwell::attributes::Attribute::get_named_enum_kind_id("noinline");
        let attr = self.ctx.create_enum_attribute(kind, 0);
        let mut f = self.module.get_first_function();
        while let Some(func) = f {
            let blocks = func.count_basic_blocks();
            // Skip declarations, large bodies and explicitly out-of-line helpers.
            if blocks > 0
                && blocks <= SMALL_BLOCKS
                && func
                    .get_enum_attribute(inkwell::attributes::AttributeLoc::Function, noinline)
                    .is_none()
            {
                func.add_attribute(inkwell::attributes::AttributeLoc::Function, attr);
            }
            f = func.get_next_function();
        }
    }

    /// Emit `__pp_freeze_globals`: a `void()` function that loads each immutable
    /// heap global and deep-freezes it. The entry sequence calls it once after
    /// module init so the namespace is frozen before `main` runs. No-op
    /// (function still emitted, empty) when there are no immutable heap globals.
    pub(super) fn emit_freeze_globals_fn(&mut self) {
        let fty = self.ctx.void_type().fn_type(&[], false);
        let func = self.module.add_function(FREEZE_GLOBALS_FN, fty, None);
        let entry = self.ctx.append_basic_block(func, "entry");
        self.builder.position_at_end(entry);
        let freeze_ty = self
            .ctx
            .void_type()
            .fn_type(&[self.abi.ptr().into()], false);
        let freeze = self
            .abi
            .runtime_fn(&self.module, "pp_freeze_deep", freeze_ty);
        let names: Vec<String> = self.mir.frozen_globals.clone();
        for name in names {
            if let Some(g) = self.mir.globals.get(&name) {
                // The global slot holds the heap pointer; load it and freeze it.
                let ptr = self
                    .builder
                    .build_load(self.abi.ptr(), g.as_pointer_value(), "gv")
                    .unwrap();
                self.builder.build_call(freeze, &[ptr.into()], "").unwrap();
            }
        }
        self.builder.build_return(None).unwrap();
    }

    /// Run LLVM's `default<O2>` pipeline over the module (which subsumes the
    /// always-inliner, so the `alwaysinline` marks above take effect too).
    /// Codegen builds every local as a stack slot; without the mid-level
    /// pipeline (mem2reg/SROA, instcombine, LICM, GVN) each MIR statement
    /// keeps its memory round-trip and hot loops run several times slower
    /// than the equivalent register-form code. Best-effort: optimization is
    /// not required for correctness, so a pass-setup failure is non-fatal.
    pub(super) fn run_optimization_passes(&self) {
        use inkwell::passes::PassBuilderOptions;
        use inkwell::targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine};

        // The native target must be registered before the triple resolves.
        // The JIT engine does this itself, but it is created after this pass
        // runs, so resolve it here or `Target::from_triple` fails and the
        // whole pipeline is silently skipped.
        if Target::initialize_native(&InitializationConfig::default()).is_err() {
            return;
        }
        let triple = TargetMachine::get_default_triple();
        let Ok(target) = Target::from_triple(&triple) else {
            return;
        };
        let Some(machine) = target.create_target_machine(
            &triple,
            "generic",
            "",
            OptimizationLevel::Default,
            RelocMode::Default,
            CodeModel::Default,
        ) else {
            return;
        };
        if let Err(e) =
            self.module
                .run_passes("default<O2>", &machine, PassBuilderOptions::create())
        {
            tracing::warn!(target: "brass::ir", "optimization pipeline failed: {e}");
        }
    }

    /// The JIT machine address of a compiled instance by its instance symbol
    /// (after [`EngineCodegen::finalize`]), for embedding and tests that call a
    /// non-entry instance directly. For lazy groups this looks up the hidden
    /// implementation, materializing immediately; deferred slots receive the
    /// body address and never a first-call stub. Unknown instances return None.
    pub fn address_of(&self, instance_symbol: &str) -> Option<usize> {
        let public = mangle_fn(instance_symbol);
        let lazy = *self.mir.defined.get(&public)?;
        let symbol = if lazy {
            lazy_implementation_symbol(&public)
        } else {
            public
        };
        self.mir.orc.as_ref()?.lookup(&symbol).ok()
    }

    /// Whether an instance already has a definition in this session, without
    /// triggering materialization. Used to deduplicate runtime batches.
    pub fn has_instance(&self, symbol: &str) -> bool {
        self.mir.defined.contains_key(&mangle_fn(symbol))
    }

    /// Run a zero-argument instance returning i32 after finalization.
    pub fn run_entry_i32(&self, name: &str) -> Option<i32> {
        self.address_of(name).map(crate::dispatch::call_i32)
    }

    /// Run a zero-argument instance returning i64 after finalization.
    pub fn run_entry_i64(&self, name: &str) -> Option<i64> {
        self.address_of(name).map(crate::dispatch::call_i64)
    }

    /// Run a zero-argument instance returning f64 after finalization.
    pub fn run_entry_f64(&self, name: &str) -> Option<f64> {
        self.address_of(name).map(crate::dispatch::call_f64)
    }

    /// The printed LLVM type of a compiled instance's function (e.g.
    /// `"i32 (i32)"`), for verifying the typed/unboxed signature in tests.
    pub fn instance_fn_type_string(&self, name: &str) -> Option<String> {
        let f = self.module.get_function(&mangle_fn(name))?;
        Some(f.get_type().print_to_string().to_string())
    }
}

#[cfg(test)]
mod managed_global_tests {
    use super::*;
    use brass_hir::IntKind;

    #[test]
    fn every_managed_pointer_shape_is_freezable() {
        // Global freezing follows the runtime representation through mode wrappers.
        let managed = [
            Type::Array(Box::new(Type::Bool), 2),
            Type::Tuple(vec![Type::Bool, Type::Str]),
            Type::Fun(Vec::new(), Box::new(Type::Void)),
            Type::Ref(Box::new(Type::Mut(Box::new(Type::Slice(Box::new(
                Type::Str,
            )))))),
        ];
        assert!(managed.iter().all(is_heap_pointer_type));
        assert!(!is_heap_pointer_type(&Type::Int(IntKind::I64)));
    }
}
