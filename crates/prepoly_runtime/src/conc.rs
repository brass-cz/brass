//! Concurrency runtime: real-thread `spawn` and the cown acquire/release lock. The language exposes only `spawn(f)` and `with(cown, f)`; the
//! compiler decides ownership (move/freeze/cown) and inserts acquire/release, so
//! these primitives are the dynamic half of the two-stage safety model: a cown's
//! shared mutable object is reached only while its lock is held, which makes
//! concurrent access data-race-free at runtime.
//!
//! A spawned closure's captures are made safe by the ownership analysis before
//! they reach another thread (moved when unique, frozen when read-only, or cowned
//! when mutated), so transferring the closure pointer across threads is sound.

use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};
use std::thread::JoinHandle;

use crate::rt::{Header, OWNER_COWN};

/// Count of spawned threads that have not yet finished their heap work. The cycle
/// collector reads this to defer collection while any spawned thread runs: it
/// mutates object headers non-atomically, so it must run only when the main
/// thread is the sole mutator (see `crate::gc::pp_gc_collect`).
static ACTIVE_SPAWNS: AtomicUsize = AtomicUsize::new(0);

/// Whether any spawned thread is currently running.
pub fn has_active_spawns() -> bool {
    ACTIVE_SPAWNS.load(Ordering::SeqCst) > 0
}

/// A heap pointer asserted `Send`. The compiler's ownership analysis guarantees a
/// spawned closure's reachable mutable state is exclusive (moved), immutable
/// (frozen), or lock-guarded (cown), so handing the closure to another thread
/// cannot create a data race despite the raw pointer.
struct SendPtr(*mut Header);
unsafe impl Send for SendPtr {}

/// Spawned thread handles, joined before the program exits so spawned work
/// completes and program output is deterministic.
fn threads() -> &'static Mutex<Vec<JoinHandle<()>>> {
    static THREADS: OnceLock<Mutex<Vec<JoinHandle<()>>>> = OnceLock::new();
    THREADS.get_or_init(|| Mutex::new(Vec::new()))
}

/// Promote `obj` to a cown so its reference count is maintained atomically (the
/// `rc_atomic` class) and it is safe to share across threads, while it stays
/// mutable -- reached only under its lock via `with`. The compiler calls this on a
/// `spawn` capture the closure mutates, *before* the spawn, so the owner (and thus
/// the count's atomicity) is fixed before the first cross-thread reference; a later
/// `with` re-tags it as the region bridge, which is also an `rc_atomic` class, so
/// the count stays atomic across that transition. Shallow: the region interior is
/// governed by the `with` region barrier.
///
/// # Safety
/// `obj` must be a valid object header (or null).
pub unsafe extern "C-unwind" fn pp_make_cown(obj: *mut Header) {
    unsafe {
        if !obj.is_null() {
            (*obj).owner = OWNER_COWN;
        }
    }
}

/// The lock byte of a heap object: the header's `flags` field (offset 11),
/// accessed atomically. `0` = free, `1` = held. The bump allocator zeroes it and
/// never otherwise uses it, so a per-object spinlock can live there.
unsafe fn lock_byte<'a>(obj: *mut Header) -> &'a AtomicU8 {
    unsafe { &*((obj as *mut u8).add(11) as *const AtomicU8) }
}

/// Acquire a cown's lock, spinning until it is free.
/// Short critical sections make a spinlock the efficient choice; an uncontended
/// acquire is a single successful compare-exchange.
///
/// # Safety
/// `obj` must be a valid object header (or null).
pub unsafe extern "C-unwind" fn pp_lock(obj: *mut Header) {
    if obj.is_null() {
        return;
    }
    let lock = unsafe { lock_byte(obj) };
    while lock
        .compare_exchange_weak(0, 1, Ordering::Acquire, Ordering::Relaxed)
        .is_err()
    {
        std::hint::spin_loop();
    }
}

/// Release a cown's lock.
///
/// # Safety
/// `obj` must be a valid object header (or null).
pub unsafe extern "C-unwind" fn pp_unlock(obj: *mut Header) {
    if obj.is_null() {
        return;
    }
    unsafe { lock_byte(obj) }.store(0, Ordering::Release);
}

/// The cown pointers held in a growable array `{ header16 | len@16 | data@32 }`,
/// sorted by address and de-duplicated. Sorting gives a global lock order so
/// `with([a, b], ..)` over several cowns cannot deadlock against `with([b, a],
/// ..)`; de-duplication avoids self-deadlock on a repeated cown.
unsafe fn array_cowns(arr: *mut Header) -> Vec<*mut Header> {
    unsafe {
        if arr.is_null() {
            return Vec::new();
        }
        let len = *((arr as *mut u8).add(16) as *mut i64);
        let data = *((arr as *mut u8).add(32) as *mut *mut *mut Header);
        let mut ptrs: Vec<*mut Header> = (0..len).map(|i| *data.offset(i as isize)).collect();
        ptrs.sort_unstable_by_key(|p| *p as usize);
        ptrs.dedup();
        ptrs
    }
}

/// Acquire every cown in an array, in a deterministic (address) order so
/// multiple `with([..])` acquisitions cannot deadlock.
///
/// # Safety
/// `arr` must be a growable-array object of cown pointers (or null).
pub unsafe extern "C-unwind" fn pp_lock_all(arr: *mut Header) {
    unsafe {
        for p in array_cowns(arr) {
            pp_lock(p);
        }
    }
}

/// Release every cown in an array (reverse acquisition order).
///
/// # Safety
/// `arr` must be a growable-array object of cown pointers (or null).
pub unsafe extern "C-unwind" fn pp_unlock_all(arr: *mut Header) {
    unsafe {
        for p in array_cowns(arr).into_iter().rev() {
            pp_unlock(p);
        }
    }
}

/// Spawn a closure on a new OS thread. The closure is the
/// `{ header | fn-ptr@16 | captures... }` object the typed back end builds; a
/// zero-argument closure's compiled signature is `void(env)`, so the thread calls
/// the function pointer with the closure object as its environment.
pub extern "C-unwind" fn pp_spawn(closure: *mut Header) {
    let captured = SendPtr(closure);
    // Mark a spawn active before the thread starts and clear it only after the
    // thread's last heap operation, so the cycle collector defers while it runs.
    ACTIVE_SPAWNS.fetch_add(1, Ordering::SeqCst);
    let handle = std::thread::spawn(move || {
        // Bind the whole `SendPtr` so the closure captures it (which is `Send`),
        // not its raw pointer field (disjoint capture would not be `Send`).
        let captured = captured;
        let env = captured.0;
        unsafe {
            let fnptr = *((env as *mut u8).add(16) as *mut usize);
            let f: extern "C" fn(*mut Header) = std::mem::transmute(fnptr);
            f(env);
            // The spawner moved the closure to this thread (its reference, not a
            // retained copy). Release it via its stored destructor (offset 24),
            // which releases the captures and frees the environment.
            let dtor_ptr = *((env as *mut u8).add(24) as *mut usize);
            if dtor_ptr != 0 {
                let dtor: extern "C" fn(*mut Header) = std::mem::transmute(dtor_ptr);
                dtor(env);
            }
        }
        // Heap work done; allow collection again once every thread has cleared.
        ACTIVE_SPAWNS.fetch_sub(1, Ordering::SeqCst);
    });
    threads().lock().unwrap().push(handle);
}

/// Join every spawned thread. The driver calls this in `main`'s epilogue so the
/// program waits for spawned work before exiting. With all threads joined the main
/// thread is again the sole mutator, so it runs a collection to reclaim any cycle
/// garbage whose collection was deferred while spawned threads ran.
pub extern "C-unwind" fn pp_join_all() {
    // A spawned thread may itself spawn (a nested/late spawn), pushing a new handle
    // after this drain started. Loop until the registry stays empty: each round
    // joins the threads taken so far, during which any of them may have pushed more.
    // Without this, a nested spawn is never joined -- its work is lost and it runs
    // into process teardown, a use-after-free of runtime state.
    loop {
        let handles: Vec<_> = std::mem::take(&mut *threads().lock().unwrap());
        if handles.is_empty() {
            break;
        }
        for h in handles {
            let _ = h.join();
        }
    }
    crate::gc::pp_gc_collect();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mem::pp_obj_alloc;
    use std::sync::MutexGuard;
    use std::sync::atomic::{AtomicI64, Ordering};

    /// `pp_join_all` drains a *global* thread registry, so two spawn-using tests
    /// running in parallel would join each other's threads. Each such test holds
    /// this lock for its duration, serializing them (a real program has a single
    /// `main`, so the global registry is correct there).
    fn serial_spawn() -> MutexGuard<'static, ()> {
        crate::serial_heap_test()
    }

    /// Allocate a 24-byte object (16-byte header + one i64 field at offset 16).
    fn alloc_counter() -> *mut Header {
        unsafe { pp_obj_alloc(24) as *mut Header }
    }

    unsafe fn field(obj: *mut Header) -> *mut i64 {
        unsafe { (obj as *mut u8).add(16) as *mut i64 }
    }

    #[test]
    fn lock_gives_mutual_exclusion_under_real_threads() {
        // Many threads each acquire the same object's lock, read-modify-write its
        // counter field, and release. A data race would lose increments; the lock
        // must serialize them so the final count is exact. Run via the actual
        // `pp_spawn`/`pp_join_all` path with closure-shaped objects.
        let _serial = serial_spawn();
        let counter = alloc_counter();
        unsafe { *field(counter) = 0 };

        const THREADS: i64 = 8;
        const PER_THREAD: i64 = 5000;

        // The work each spawned closure runs: lock, bump PER_THREAD times, unlock.
        extern "C" fn work(env: *mut Header) {
            // The captured counter pointer is at the closure env's first capture
            // slot, offset 32 (see the closure layout below).
            let counter = unsafe { *((env as *mut u8).add(32) as *mut *mut Header) };
            for _ in 0..PER_THREAD {
                unsafe { pp_lock(counter) };
                unsafe {
                    let f = field(counter);
                    *f += 1;
                }
                unsafe { pp_unlock(counter) };
            }
        }

        for _ in 0..THREADS {
            // A closure object shaped like the back end's: `{ header(16) | fn@16 |
            // dtor@24 | captures@32 }`. `pp_spawn` calls the function at @16 and then
            // the destructor at @24, so the destructor slot is left zero (no dtor)
            // and the captured counter goes in the first capture slot at @32.
            let clo = unsafe { pp_obj_alloc(40) as *mut Header };
            unsafe {
                *((clo as *mut u8).add(16) as *mut usize) = work as *const () as usize;
                *((clo as *mut u8).add(32) as *mut *mut Header) = counter;
            }
            pp_spawn(clo);
        }
        pp_join_all();

        assert_eq!(
            unsafe { *field(counter) },
            THREADS * PER_THREAD,
            "every increment must survive: no lost updates under contention"
        );
    }

    #[test]
    fn spawned_threads_actually_run_concurrently() {
        // Beyond mutual exclusion, the threads must really run: a shared atomic
        // bumped once per spawned closure reaches the spawn count after join.
        let _serial = serial_spawn();
        static RAN: AtomicI64 = AtomicI64::new(0);
        RAN.store(0, Ordering::SeqCst);

        extern "C" fn bump(_env: *mut Header) {
            RAN.fetch_add(1, Ordering::SeqCst);
        }

        const N: i64 = 16;
        for _ in 0..N {
            // `{ header(16) | fn@16 | dtor@24 }` -- 32 bytes so the destructor slot
            // `pp_spawn` reads at @24 is in bounds and zero (this closure has no
            // captures and no destructor).
            let clo = unsafe { pp_obj_alloc(32) as *mut Header };
            unsafe { *((clo as *mut u8).add(16) as *mut usize) = bump as *const () as usize };
            pp_spawn(clo);
        }
        pp_join_all();
        assert_eq!(RAN.load(Ordering::SeqCst), N, "all spawned closures ran");
    }

    #[test]
    fn join_all_drains_nested_spawns() {
        // A spawned thread that itself spawns must have its child joined too: after
        // `pp_join_all` the grandchild's effect is observed. Before the drain loop,
        // the nested handle was pushed to the registry after the single `take` and
        // never joined -- its work was lost and it ran into process teardown.
        let _serial = serial_spawn();
        static RAN: AtomicI64 = AtomicI64::new(0);
        RAN.store(0, Ordering::SeqCst);

        extern "C" fn grandchild(_env: *mut Header) {
            RAN.fetch_add(1, Ordering::SeqCst);
        }
        extern "C" fn parent(_env: *mut Header) {
            // Spawn a grandchild from inside this already-spawned thread.
            let clo = unsafe { pp_obj_alloc(32) as *mut Header };
            unsafe { *((clo as *mut u8).add(16) as *mut usize) = grandchild as *const () as usize };
            pp_spawn(clo);
        }

        let clo = unsafe { pp_obj_alloc(32) as *mut Header };
        unsafe { *((clo as *mut u8).add(16) as *mut usize) = parent as *const () as usize };
        pp_spawn(clo);
        pp_join_all();
        assert_eq!(
            RAN.load(Ordering::SeqCst),
            1,
            "the nested spawn was joined and its work ran"
        );
    }

    #[test]
    fn lock_all_is_deadlock_free_across_array_orders() {
        // Two threads repeatedly acquire the same two cowns via `pp_lock_all`, but
        // through arrays in opposite orders ([a,b] vs [b,a]). Address-ordered
        // acquisition gives one global lock order, so they cannot deadlock; both
        // finish (the join returns) and each counter receives every increment.
        let _serial = serial_spawn();
        let a = alloc_counter();
        let b = alloc_counter();
        unsafe {
            *field(a) = 0;
            *field(b) = 0;
        }

        // A 2-element growable array `{ header | len@16 | _cap@24 | data@32 }`.
        unsafe fn arr2(x: *mut Header, y: *mut Header) -> *mut Header {
            unsafe {
                let arr = pp_obj_alloc(40) as *mut Header;
                *((arr as *mut u8).add(16) as *mut i64) = 2;
                let buf = pp_obj_alloc(16) as *mut *mut Header;
                *buf = x;
                *buf.add(1) = y;
                *((arr as *mut u8).add(32) as *mut *mut *mut Header) = buf;
                arr
            }
        }

        const PER_THREAD: i64 = 4000;
        // The closure env is `{ header | fn@16 | dtor@24 | array@32 }`; the worker
        // locks all cowns in the array, bumps both counters, and unlocks.
        extern "C" fn work(env: *mut Header) {
            let arr = unsafe { *((env as *mut u8).add(32) as *mut *mut Header) };
            for _ in 0..PER_THREAD {
                unsafe { pp_lock_all(arr) };
                unsafe {
                    let cowns = array_cowns(arr);
                    for c in cowns {
                        *field(c) += 1;
                    }
                }
                unsafe { pp_unlock_all(arr) };
            }
        }

        for arr in [unsafe { arr2(a, b) }, unsafe { arr2(b, a) }] {
            // `{ header(16) | fn@16 | dtor@24 (zero) | array@32 }` -- the captured
            // array goes in the first capture slot at @32, leaving the destructor
            // slot `pp_spawn` reads at @24 zero.
            let clo = unsafe { pp_obj_alloc(40) as *mut Header };
            unsafe {
                *((clo as *mut u8).add(16) as *mut usize) = work as *const () as usize;
                *((clo as *mut u8).add(32) as *mut *mut Header) = arr;
            }
            pp_spawn(clo);
        }
        pp_join_all();

        // Both threads ran to completion (no deadlock) and every increment landed.
        assert_eq!(unsafe { *field(a) }, 2 * PER_THREAD);
        assert_eq!(unsafe { *field(b) }, 2 * PER_THREAD);
    }

    #[test]
    fn shared_object_refcount_is_atomic_under_threads() {
        // A `Bridge`-owned object (a `with`-acquired cown a spawn capture is
        // promoted to) is shared across threads, so its reference count must be
        // atomic -- a non-atomic increment/decrement loses updates under
        // contention, which leaks or double-frees. Many threads each do balanced
        // retain/release; with atomic counting the count returns exactly to its
        // start. (Before the `rc_atomic` fix, `Bridge` used the non-atomic path and
        // this lost updates.)
        use crate::alloc::{pp_release, pp_retain};
        use crate::mem::pp_live_blocks;
        use crate::rt::OWNER_BRIDGE;

        let _serial = serial_spawn();
        let obj = alloc_counter();
        unsafe {
            (*obj).rc = 1;
            (*obj).owner = OWNER_BRIDGE;
        }
        let before = pp_live_blocks();
        let addr = obj as usize;

        const THREADS: usize = 8;
        const PER_THREAD: usize = 20_000;
        let handles: Vec<_> = (0..THREADS)
            .map(|_| {
                std::thread::spawn(move || {
                    let obj = addr as *mut Header;
                    for _ in 0..PER_THREAD {
                        unsafe {
                            pp_retain(obj);
                            pp_release(obj);
                        }
                    }
                })
            })
            .collect();
        for h in handles {
            h.join().unwrap();
        }

        // The base reference is held throughout, so every thread's retain leads its
        // release and the count never drops to zero mid-run; it returns to 1.
        assert_eq!(unsafe { (*obj).rc }, 1, "no lost reference-count updates");
        assert_eq!(
            pp_live_blocks(),
            before,
            "object neither leaked nor freed early"
        );
        unsafe { pp_release(obj) };
        assert_eq!(
            pp_live_blocks(),
            before - 1,
            "the final release frees it exactly once"
        );
    }
}
