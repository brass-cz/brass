//! The runtime dispatch service for deferred monomorphization.
//!
//! When a type is fixed by the outside world at runtime (e.g. JSON deserialize),
//! the consumer of that value must be specialized and JIT-compiled *then*. This
//! module holds the live compiler service -- the MIR template program, the HIR
//! program, the running LLVM backend, and the runtime [`MonomorphCache`] -- and
//! exposes the [`pp_resolve`] trampoline that generated code calls to obtain (and
//! lazily compile) the consumer specialized for a boundary value's runtime type.
//!
//! The service is reached through a thread-local raw pointer installed for the
//! duration of the program run ([`with_dispatcher`]); the pointer is only valid
//! while installed, and the trampoline is only emitted at deferred call sites, so
//! it is never reached otherwise.

use std::cell::Cell;
use std::ptr;

use brass_engine::{
    MonomorphCache, RuntimeJit, boundary_record_type_by_name, boundary_record_type_from_fields,
    instance_symbol, monomorphize_instance, parse_structural_descriptor,
};
use brass_hir::Program;
use brass_mir::MirProgram;

use crate::codegen::LlvmCodegen;

/// The live deferred-monomorphization service: the MIR template program, the HIR
/// program, the running JIT backend, and the runtime cache of compiled instances.
pub struct RuntimeDispatcher<'a, 'ctx, 'p> {
    mir: &'a MirProgram,
    program: &'a Program,
    backend: &'a mut LlvmCodegen<'ctx, 'p>,
    cache: MonomorphCache,
}

impl<'a, 'ctx, 'p> RuntimeDispatcher<'a, 'ctx, 'p> {
    pub fn new(
        mir: &'a MirProgram,
        program: &'a Program,
        backend: &'a mut LlvmCodegen<'ctx, 'p>,
    ) -> Self {
        Self {
            mir,
            program,
            backend,
            cache: MonomorphCache::new(),
        }
    }

    /// Resolve -- compiling on first use, caching after -- the consumer `base`
    /// specialized for a runtime type, returning its callable address. The type is
    /// given either by name (a declared type) or, when `type_name` is a structural
    /// descriptor (`"field:tag,..."`), built data-driven from that
    /// descriptor. Errors if the type is unfit (it lacks a field the consumer
    /// reads): the boundary's structural check, enforced before specialization
    /// rather than miscompiled.
    pub fn resolve(&mut self, base: &str, type_name: &str) -> Result<usize, String> {
        // A descriptor (data-driven `Type::Record`) over a declared-type name: a
        // ':' separates a field from its type tag, which a type name never has.
        let ty = if type_name.contains(':') {
            let fields = parse_structural_descriptor(type_name)
                .ok_or_else(|| format!("malformed structural type descriptor `{type_name}`"))?;
            boundary_record_type_from_fields(&fields)
        } else {
            boundary_record_type_by_name(self.program, type_name)
                .ok_or_else(|| format!("no record type named `{type_name}`"))?
        };
        let inst = instance_symbol(base, std::slice::from_ref(&ty));
        if let Some(addr) = self.cache.get(&inst) {
            return Ok(addr);
        }
        let mono = monomorphize_instance(self.mir, self.program, base, vec![ty])?;
        let f = mono
            .lookup(&inst)
            .ok_or_else(|| format!("no instance `{inst}`"))?;
        let addr = self.backend.compile_instance(&mono, f)?;
        self.cache.insert(inst, addr);
        Ok(addr)
    }
}

thread_local! {
    /// Raw pointer to the [`RuntimeDispatcher`] installed for the current run.
    static CURRENT: Cell<*mut ()> = const { Cell::new(ptr::null_mut()) };
}

/// Install `dispatcher` as this thread's dispatch service for the duration of
/// `body` (running `main`), so [`pp_resolve`] reaches it. The raw pointer is valid
/// only within `body`; `body` must not otherwise touch `dispatcher` (the
/// trampoline uses the pointer reentrantly).
pub fn with_dispatcher<R>(dispatcher: &mut RuntimeDispatcher, body: impl FnOnce() -> R) -> R {
    let ptr = dispatcher as *mut RuntimeDispatcher as *mut ();
    let prev = CURRENT.with(|c| c.replace(ptr));
    let out = body();
    CURRENT.with(|c| c.set(prev));
    out
}

/// Deferred-site addresses already resolved, readable from ANY thread. A
/// worker thread executing spawned code answers its deferred calls here --
/// workers cannot compile (the LLVM engine lives on the main thread), so the
/// main thread primes every recorded target before a spawning batch runs
/// (see the driver's spawn drain), and this cache is how those answers
/// cross threads. Keyed by instance symbol (the empty-type-string flavor of
/// [`pp_resolve`]).
static RESOLVED: std::sync::LazyLock<std::sync::RwLock<fxhash::FxHashMap<String, usize>>> =
    std::sync::LazyLock::new(|| std::sync::RwLock::new(fxhash::FxHashMap::default()));

/// Record a resolved deferred-site address for every thread to read.
pub fn prime_resolved(symbol: &str, addr: usize) {
    if let Ok(mut map) = RESOLVED.write() {
        map.insert(symbol.to_string(), addr);
    }
}

/// The lazy JIT's resolver, type-erased for the thread-local slot: the
/// backend the resolver may compile into, and the driver's resolution
/// closure (which owns the checker channels and the growing MIR program).
/// Split so the closure receives the backend re-materialized -- the two
/// live in one slot precisely because `pp_resolve` is entered from JIT
/// code while `execute_deferred` holds the backend.
struct DeferredSlot {
    backend: *mut (),
    resolve: *mut (),
}

thread_local! {
    /// The [`DeferredSlot`] installed for the current lazy run.
    static CURRENT_DEFERRED: Cell<*mut ()> = const { Cell::new(ptr::null_mut()) };
}

/// Install the lazy resolver for the duration of `body` (running the
/// program), so [`pp_resolve`] reaches it. Same discipline as
/// [`with_dispatcher`]: the raw pointers are valid only within `body`, and
/// `body` must not otherwise touch the backend or the closure.
pub(crate) fn with_deferred_resolver<'ctx, 'p, R>(
    backend: &mut crate::codegen::LlvmCodegen<'ctx, 'p>,
    resolve: &mut dyn FnMut(&mut crate::codegen::LlvmCodegen<'ctx, 'p>, &str) -> usize,
    body: impl FnOnce() -> R,
) -> R {
    let mut resolve = resolve;
    let mut slot = DeferredSlot {
        backend: backend as *mut crate::codegen::LlvmCodegen<'ctx, 'p> as *mut (),
        resolve: &mut resolve
            as *mut &mut dyn FnMut(&mut crate::codegen::LlvmCodegen<'ctx, 'p>, &str) -> usize
            as *mut (),
    };
    let prev = CURRENT_DEFERRED.with(|c| c.replace(&mut slot as *mut DeferredSlot as *mut ()));
    let out = body();
    CURRENT_DEFERRED.with(|c| c.set(prev));
    out
}

/// The dispatch trampoline generated code calls: resolve-or-
/// compile the consumer named by `[name_ptr, name_len]` for the runtime type
/// named by `[type_ptr, type_len]`, returning its callable address (0 if no
/// service is installed, a name is invalid, or the type is unfit -- the caller
/// treats 0 as a failed dispatch).
///
/// # Safety
/// Call only while a [`RuntimeDispatcher`] is installed on this thread (within
/// [`with_dispatcher`]); the two `(ptr, len)` pairs must describe valid UTF-8.
pub unsafe extern "C" fn pp_resolve(
    name_ptr: *const u8,
    name_len: usize,
    type_ptr: *const u8,
    type_len: usize,
) -> usize {
    unsafe {
        // The lazy JIT's sites pass the instance symbol with an empty type
        // string. Already-resolved targets answer from the cross-thread
        // cache -- the only path a worker thread (spawned code) can take,
        // and the fast path for everyone else.
        if type_len == 0 {
            let name = std::str::from_utf8(std::slice::from_raw_parts(name_ptr, name_len));
            if let Ok(name) = name
                && let Ok(map) = RESOLVED.read()
                && let Some(&addr) = map.get(name)
            {
                return addr;
            }
        }
        // The compiling resolver: main-thread only. A worker reaching a
        // target the spawn drain did not prime reads null here and the site
        // traps -- kept defined, and unreachable while the drain invariant
        // holds.
        let deferred = CURRENT_DEFERRED.with(|c| c.get());
        if !deferred.is_null() {
            let slot = &mut *(deferred as *mut DeferredSlot);
            let backend =
                &mut *(slot.backend as *mut crate::codegen::LlvmCodegen<'static, 'static>);
            let resolve = &mut *(slot.resolve
                as *mut &mut dyn FnMut(
                    &mut crate::codegen::LlvmCodegen<'static, 'static>,
                    &str,
                ) -> usize);
            let Some(name) =
                std::str::from_utf8(std::slice::from_raw_parts(name_ptr, name_len)).ok()
            else {
                return 0;
            };
            return resolve(backend, name);
        }
        let cur = CURRENT.with(|c| c.get());
        if cur.is_null() {
            return 0;
        }
        // The installed dispatcher outlives every call made within `with_dispatcher`;
        // its concrete lifetimes are erased through the raw pointer but its borrows are
        // live, so the methods operate on valid data.
        let dispatcher = &mut *(cur as *mut RuntimeDispatcher<'static, 'static, 'static>);
        let utf8 = |ptr, len| std::str::from_utf8(std::slice::from_raw_parts(ptr, len)).ok();
        let (Some(name), Some(type_name)) = (utf8(name_ptr, name_len), utf8(type_ptr, type_len))
        else {
            return 0;
        };
        dispatcher.resolve(name, type_name).unwrap_or(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen::LlvmCodegen;
    use brass_engine::Codegen;
    use inkwell::context::Context;

    /// The full in-engine deferred flow through the trampoline: a deferred-param
    /// consumer is resolved-and-compiled for a runtime type via `pp_resolve` and
    /// run on a value of that type. `pp_resolve` is called directly here (as
    /// generated code would), exercising the service + trampoline end to end.
    #[test]
    fn pp_resolve_compiles_and_returns_a_consumer_for_a_runtime_type() {
        let src = "type Person = {\n  age: int32\n}\n\
                   fun get_age(p) -> int32 {\n  return p.age\n}\n\
                   fun main() {\n}\n";
        let ast = brass_parser::parse(src).expect("parse");
        let (program, errs) = brass_hir::lower(&[brass_hir::LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errs.is_empty(), "lower: {errs:?}");
        let mir = brass_mir::lower_program(&program);
        let static_mono = brass_engine::monomorphize(&mir, &program).expect("monomorphize");
        let get_age = mir
            .functions
            .iter()
            .find(|f| f.name == "get_age")
            .map(|f| f.symbol.clone())
            .expect("get_age");
        let ty = "Person";

        let ctx = Context::create();
        let mut backend = LlvmCodegen::new_backend(&ctx, &program);
        backend.begin_program(&static_mono);
        backend.finalize().expect("finalize");

        let mut dispatcher = RuntimeDispatcher::new(&mir, &program, &mut backend);
        let addr = with_dispatcher(&mut dispatcher, || unsafe {
            pp_resolve(get_age.as_ptr(), get_age.len(), ty.as_ptr(), ty.len())
        });
        assert!(addr != 0, "trampoline resolved + compiled the consumer");

        // Run it on a `Person { age: 42 }` boundary value (header16 | age@16).
        let mut storage = [0u64; 3];
        storage[2] = 42;
        let get_age_fn: extern "C" fn(*mut std::ffi::c_void) -> i32 =
            unsafe { std::mem::transmute(addr) };
        assert_eq!(
            get_age_fn(storage.as_mut_ptr() as *mut std::ffi::c_void),
            42
        );

        // No service installed -> the trampoline reports a failed dispatch (0).
        let miss = unsafe { pp_resolve(get_age.as_ptr(), get_age.len(), ty.as_ptr(), ty.len()) };
        assert_eq!(miss, 0, "no dispatcher installed -> 0");
    }

    /// Deferred monomorphization from a *structural* descriptor: the
    /// consumer's argument type is built data-driven from `"score:int32"` -- no
    /// declared record has a `score` field -- then specialized and run on a value of
    /// that shape. This exercises the data-driven `Type::Record` construction the
    /// named-lookup path does not.
    #[test]
    fn pp_resolve_builds_a_structural_type_from_a_descriptor() {
        let src = "fun get_score(p) -> int32 {\n  return p.score\n}\n\
                   fun main() {\n}\n";
        let ast = brass_parser::parse(src).expect("parse");
        let (program, errs) = brass_hir::lower(&[brass_hir::LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errs.is_empty(), "lower: {errs:?}");
        let mir = brass_mir::lower_program(&program);
        let static_mono = brass_engine::monomorphize(&mir, &program).expect("monomorphize");
        let get_score = mir
            .functions
            .iter()
            .find(|f| f.name == "get_score")
            .map(|f| f.symbol.clone())
            .expect("get_score");
        let descriptor = "score:int32";

        let ctx = Context::create();
        let mut backend = LlvmCodegen::new_backend(&ctx, &program);
        backend.begin_program(&static_mono);
        backend.finalize().expect("finalize");

        let mut dispatcher = RuntimeDispatcher::new(&mir, &program, &mut backend);
        let addr = with_dispatcher(&mut dispatcher, || unsafe {
            pp_resolve(
                get_score.as_ptr(),
                get_score.len(),
                descriptor.as_ptr(),
                descriptor.len(),
            )
        });
        assert!(
            addr != 0,
            "structural descriptor resolved + compiled the consumer"
        );

        // Run it on a `{ score: 7 }` boundary value (header16 | score@16).
        let mut storage = [0u64; 3];
        storage[2] = 7;
        let get_score_fn: extern "C" fn(*mut std::ffi::c_void) -> i32 =
            unsafe { std::mem::transmute(addr) };
        assert_eq!(
            get_score_fn(storage.as_mut_ptr() as *mut std::ffi::c_void),
            7
        );
    }
}
