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

use prepoly_engine::{
    MonomorphCache, RuntimeJit, boundary_record_type_by_name, boundary_record_type_from_fields,
    instance_symbol, monomorphize_instance, parse_structural_descriptor,
};
use prepoly_hir::Program;
use prepoly_mir::MirProgram;

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
    use inkwell::context::Context;
    use prepoly_engine::Codegen;

    /// The full in-engine deferred flow through the trampoline: a deferred-param
    /// consumer is resolved-and-compiled for a runtime type via `pp_resolve` and
    /// run on a value of that type. `pp_resolve` is called directly here (as
    /// generated code would), exercising the service + trampoline end to end.
    #[test]
    fn pp_resolve_compiles_and_returns_a_consumer_for_a_runtime_type() {
        let src = "type Person = {\n  age: int32\n}\n\
                   fun get_age(p) -> int32 {\n  return p.age\n}\n\
                   fun main() {\n}\n";
        let ast = prepoly_parser::parse(src).expect("parse");
        let (program, errs) = prepoly_hir::lower(&[prepoly_hir::LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errs.is_empty(), "lower: {errs:?}");
        let mir = prepoly_mir::lower_program(&program);
        let static_mono = prepoly_engine::monomorphize(&mir, &program).expect("monomorphize");
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
        let ast = prepoly_parser::parse(src).expect("parse");
        let (program, errs) = prepoly_hir::lower(&[prepoly_hir::LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errs.is_empty(), "lower: {errs:?}");
        let mir = prepoly_mir::lower_program(&program);
        let static_mono = prepoly_engine::monomorphize(&mir, &program).expect("monomorphize");
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
