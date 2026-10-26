//! The runtime resolution service behind the lazy JIT's deferred call sites.
//!
//! A deferred site (see `LlvmCodegen::deferred_call`) asks `pp_resolve` for
//! the address of the instance named by its symbol the first time execution
//! reaches it. Already-resolved symbols answer from a cross-thread cache; on
//! the main thread a miss goes to the driver's resolver, installed for the
//! duration of the run by `with_deferred_resolver`, which checks, lowers,
//! monomorphizes and compiles the instance into the live engine.
//!
//! The resolver is reached through a thread-local raw pointer that is only
//! valid while installed; deferred sites only exist in code that runs inside
//! that installation.

use std::cell::Cell;
use std::ptr;

/// Restores a thread-local service slot when a scoped installation ends.
struct SlotRestore {
    slot: &'static std::thread::LocalKey<Cell<*mut ()>>,
    previous: *mut (),
}

impl Drop for SlotRestore {
    fn drop(&mut self) {
        self.slot.with(|slot| slot.set(self.previous));
    }
}

/// Deferred-site addresses already resolved, readable from ANY thread. A
/// worker thread executing spawned code answers its deferred calls here --
/// workers cannot compile (the LLVM engine lives on the main thread), so the
/// main thread primes every recorded target before a spawning batch runs
/// (see the driver's spawn drain), and this cache is how those answers
/// cross threads. Keyed by instance symbol.
static RESOLVED: std::sync::LazyLock<std::sync::RwLock<fxhash::FxHashMap<String, usize>>> =
    std::sync::LazyLock::new(|| std::sync::RwLock::new(fxhash::FxHashMap::default()));

/// Record a resolved deferred-site address for every thread to read.
pub fn prime_resolved(symbol: &str, addr: usize) {
    if let Ok(mut map) = RESOLVED.write() {
        map.insert(symbol.to_string(), addr);
    }
}

/// Owns the resolved-address cache for one JIT execution session.
pub struct ResolvedSession {
    _private: (),
}

/// Start a resolved-address session, discarding entries from any prior run.
pub fn resolved_session() -> ResolvedSession {
    clear_resolved();
    ResolvedSession { _private: () }
}

impl Drop for ResolvedSession {
    fn drop(&mut self) {
        clear_resolved();
    }
}

/// End the current execution session's resolved-address scope.
pub(crate) fn clear_resolved() {
    if let Ok(mut map) = RESOLVED.write() {
        map.clear();
    }
}

/// The lazy JIT's resolver, type-erased for the thread-local slot: the
/// backend the resolver may compile into, and the driver's resolution
/// closure (which owns the checker channels and the growing MIR program).
/// Split so the closure receives the backend re-materialized -- the two
/// live in one slot precisely because `pp_resolve` is entered from JIT
/// code while `execute_with_resolver` installs the backend. ORC lookup may invoke
/// materializers, but those access only session-owned pending IR. No native
/// entry is called while the resolver holds its temporary exclusive borrow.
struct DeferredSlot {
    backend: *mut (),
    resolve: *mut (),
}

thread_local! {
    /// The [`DeferredSlot`] installed for the current lazy run.
    static CURRENT_DEFERRED: Cell<*mut ()> = const { Cell::new(ptr::null_mut()) };
}

/// Install the lazy resolver for the duration of `body` (running the
/// program), so [`pp_resolve`] reaches it. The raw pointers are valid only
/// within `body`, and `body` must not otherwise touch the backend or the
/// closure (the trampoline uses them reentrantly).
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
    let _restore = SlotRestore {
        slot: &CURRENT_DEFERRED,
        previous: prev,
    };
    body()
}

// These entry helpers are crate-private: callers supply addresses looked up
// from generated functions with the indicated zero-argument ABI.
pub(crate) fn call_void(address: usize) {
    // SAFETY: the caller selects a generated void() entry in a live session.
    unsafe { std::mem::transmute::<usize, extern "C" fn()>(address)() }
}
pub(crate) fn call_i32(address: usize) -> i32 {
    // SAFETY: run_entry_i32 selects an i32() entry in a live session.
    unsafe { std::mem::transmute::<usize, extern "C" fn() -> i32>(address)() }
}
pub(crate) fn call_i64(address: usize) -> i64 {
    // SAFETY: run_entry_i64 selects an i64() entry in a live session.
    unsafe { std::mem::transmute::<usize, extern "C" fn() -> i64>(address)() }
}
pub(crate) fn call_f64(address: usize) -> f64 {
    // SAFETY: run_entry_f64 selects an f64() entry in a live session.
    unsafe { std::mem::transmute::<usize, extern "C" fn() -> f64>(address)() }
}

/// The trampoline a deferred call site calls: the callable address of the
/// instance named by `[name_ptr, name_len]`, compiling it on first use. Returns
/// 0 when no resolver is installed on this thread and the symbol was not
/// primed, when the name is not UTF-8, or when the resolver could not supply
/// the instance; the site traps on 0.
///
/// # Safety
/// `[name_ptr, name_len]` must describe a readable byte range. A resolver
/// installed by [`with_deferred_resolver`] must still be live, which holds for
/// every call made from code run inside that installation.
pub(crate) unsafe extern "C" fn pp_resolve(name_ptr: *const u8, name_len: usize) -> usize {
    // SAFETY: installed scoped slots outlive this call. Execution releases all
    // compiler borrows before entering native code; resolver callbacks do not
    // execute native entries. ORC materializers use only their own session state.
    unsafe {
        let Ok(name) = std::str::from_utf8(std::slice::from_raw_parts(name_ptr, name_len)) else {
            return 0;
        };
        // Already-resolved targets answer from the cross-thread cache -- the
        // only path a worker thread (spawned code) can take, and the fast
        // path for everyone else.
        if let Ok(map) = RESOLVED.read()
            && let Some(&addr) = map.get(name)
        {
            return addr;
        }
        // The compiling resolver: main-thread only. A worker reaching a
        // target the spawn drain did not prime reads null here and the site
        // traps -- kept defined, and unreachable while the drain invariant
        // holds.
        let deferred = CURRENT_DEFERRED.with(|c| c.get());
        if deferred.is_null() {
            return 0;
        }
        let slot = &mut *(deferred as *mut DeferredSlot);
        let backend = &mut *(slot.backend as *mut crate::codegen::LlvmCodegen<'static, 'static>);
        let resolve = &mut *(slot.resolve
            as *mut &mut dyn FnMut(
                &mut crate::codegen::LlvmCodegen<'static, 'static>,
                &str,
            ) -> usize);
        resolve(backend, name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen::LlvmCodegen;
    use brass_engine::Codegen;
    use inkwell::context::Context;

    /// Resolved entries belong to one execution session and can be drained
    /// before the session's engine is released.
    #[test]
    fn resolved_entries_are_session_scoped() {
        let symbol = "__dispatch_session_scope_test";
        let session = resolved_session();
        prime_resolved(symbol, 17);
        let found = unsafe { pp_resolve(symbol.as_ptr(), symbol.len()) };
        assert_eq!(found, 17);
        drop(session);
        let missing = unsafe { pp_resolve(symbol.as_ptr(), symbol.len()) };
        assert_eq!(missing, 0, "no resolver installed and nothing primed -> 0");
    }

    /// The installed resolver answers an unprimed symbol, and the scoped slot
    /// returns to its prior (empty) state when the run unwinds.
    #[test]
    fn deferred_resolver_slot_is_scoped() {
        let ast = brass_parser::parse("fun main() {\n}\n").expect("parse");
        let (program, errs) = brass_hir::lower(&[brass_hir::LoadedModule {
            is_prelude: false,
            path: vec!["main".into()],
            ast,
        }]);
        assert!(errs.is_empty(), "lower: {errs:?}");
        let mir = brass_mir::lower_program(&program);
        let mono = brass_engine::monomorphize(&mir, &program).expect("monomorphize");
        let ctx = Context::create();
        let mut backend = LlvmCodegen::new_backend(&ctx, &program);
        backend.begin_program(&mono);

        let symbol = "__dispatch_resolver_scope_test";
        let mut resolve = |_: &mut LlvmCodegen<'_, '_>, name: &str| {
            assert_eq!(name, symbol);
            23
        };
        let found = with_deferred_resolver(&mut backend, &mut resolve, || unsafe {
            pp_resolve(symbol.as_ptr(), symbol.len())
        });
        assert_eq!(found, 23, "the installed resolver supplies the address");

        let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            with_deferred_resolver(&mut backend, &mut resolve, || panic!("test unwind"));
        }));
        assert!(unwind.is_err());
        assert!(CURRENT_DEFERRED.with(|slot| slot.get().is_null()));
    }
}
