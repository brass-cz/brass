//! Concurrency runtime: real-thread `spawn` and the cown acquire/release lock. The language exposes only `spawn(f)` and `with(cown, f)`; the
//! compiler decides ownership (move/freeze/cown) and inserts acquire/release, so
//! these primitives are the dynamic half of the two-stage safety model: a cown's
//! shared mutable object is reached only while its lock is held, which makes
//! concurrent access data-race-free at runtime.
//!
//! A spawned closure's captures are made safe by the ownership analysis before
//! they reach another thread (moved when unique, frozen when read-only, or cowned
//! when mutated), so transferring the closure pointer across threads is sound.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU8, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

use crate::rt::{Header, OWNER_COWN};

thread_local! {
    /// Per-thread reentrancy depth for each cown this thread currently holds,
    /// keyed by object address. The cross-thread spinlock byte
    /// (`lock_byte`) is the contention gate between threads; this map records how
    /// many times the *owning* thread has re-entered the lock so a nested `with`
    /// on the same cown (e.g. the auto-acquire pass guarding both a spawned
    /// closure body and the spawner's own access) does not deadlock against the
    /// non-recursive spinlock. Reentrancy is inherently per-thread, so a
    /// thread-local needs no synchronization and adds no cross-thread contention.
    static LOCK_DEPTH: RefCell<HashMap<usize, u32>> = RefCell::new(HashMap::new());
}

/// The current thread's reentrancy depth for `obj`.
fn lock_depth(obj: *mut Header) -> u32 {
    LOCK_DEPTH.with(|d| d.borrow().get(&(obj as usize)).copied().unwrap_or(0))
}

/// Record that this thread has entered `obj`'s lock once more, returning the new
/// depth.
fn push_lock_depth(obj: *mut Header) -> u32 {
    LOCK_DEPTH.with(|d| {
        let mut d = d.borrow_mut();
        let n = d.entry(obj as usize).or_insert(0);
        *n += 1;
        *n
    })
}

/// Record that this thread has left `obj`'s lock once, returning the remaining
/// depth (0 when the outermost acquisition is being released).
fn pop_lock_depth(obj: *mut Header) -> u32 {
    LOCK_DEPTH.with(|d| {
        let mut d = d.borrow_mut();
        match d.get_mut(&(obj as usize)) {
            Some(n) if *n > 1 => {
                *n -= 1;
                *n
            }
            _ => {
                d.remove(&(obj as usize));
                0
            }
        }
    })
}

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

/// The suspected-deadlock stall budget in seconds, plus one (0 = uninitialized,
/// read from `PREPOLY_LOCK_STALL_SECS` on first use; the +1 encoding lets a user
/// value of 0 -- "disable the diagnostic" -- be distinguished from uninitialized).
static STALL_SECS_PLUS_ONE: AtomicU64 = AtomicU64::new(0);

/// Default stall budget: generous enough that a legitimately long critical
/// section never trips it, short enough that a genuinely deadlocked program
/// fails in bounded time instead of hanging forever.
const DEFAULT_STALL_SECS: u64 = 30;

/// How long a contended `pp_lock` may wait before it is declared a suspected
/// deadlock. `Duration::ZERO` disables the diagnostic (spin indefinitely).
fn stall_budget() -> Duration {
    let enc = STALL_SECS_PLUS_ONE.load(Ordering::Relaxed);
    if enc != 0 {
        return Duration::from_secs(enc - 1);
    }
    let secs = std::env::var("PREPOLY_LOCK_STALL_SECS")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or(DEFAULT_STALL_SECS);
    STALL_SECS_PLUS_ONE.store(secs + 1, Ordering::Relaxed);
    Duration::from_secs(secs)
}

/// Fail loudly on a suspected deadlock: a cown lock stayed contended past the
/// stall budget, which in a correct program only happens when two threads hold
/// locks the other needs (e.g. hand-written nested `with` scopes acquiring the
/// same two cowns in opposite orders). Hanging forever would hide the bug; a
/// clear runtime error surfaces it. Under unit tests this panics (unwinds) so
/// the diagnostic is observable in-process; in a real program it exits through
/// the runtime error path.
fn stall_fail(obj: *mut Header) -> ! {
    let msg = format!(
        "suspected deadlock: the lock of cown {obj:p} was not acquired within the stall \
         budget; nested `with` scopes probably acquire the same cowns in opposite orders \
         (acquire them together with `with([a, b], ...)`, or set PREPOLY_LOCK_STALL_SECS \
         to raise the budget / 0 to disable this check)"
    );
    #[cfg(test)]
    panic!("{msg}");
    #[cfg(not(test))]
    crate::builtins::pp_panic_str(&msg)
}

/// Acquire a cown's lock, spinning until it is free. The lock is *reentrant per
/// thread*: a thread that already holds `obj` re-enters without spinning (only the
/// recursion depth grows), so nested `with` scopes on the same cown within one
/// thread do not deadlock against the non-recursive spinlock byte. Short critical
/// sections make a spinlock the efficient choice; an uncontended first acquire is
/// a single successful compare-exchange.
///
/// A contended acquire yields periodically (so a deadlocked or oversubscribed
/// program does not burn CPU pointlessly) and, after a generous wall-clock
/// budget, aborts with a suspected-deadlock error (see [`stall_fail`]) rather
/// than hanging forever. The uncontended fast path pays for none of this.
///
/// # Safety
/// `obj` must be a valid object header (or null).
pub unsafe extern "C-unwind" fn pp_lock(obj: *mut Header) {
    if obj.is_null() {
        return;
    }
    // A re-entry by the owning thread only bumps the depth; the byte stays held.
    if lock_depth(obj) > 0 {
        push_lock_depth(obj);
        return;
    }
    let lock = unsafe { lock_byte(obj) };
    let mut spins: u64 = 0;
    let mut deadline: Option<Instant> = None;
    while lock
        .compare_exchange_weak(0, 1, Ordering::Acquire, Ordering::Relaxed)
        .is_err()
    {
        spins += 1;
        // Yield now and then so a holder that lost the CPU can run; pure spinning
        // starves it on an oversubscribed machine.
        if spins & 0x3FF == 0 {
            std::thread::yield_now();
        }
        // Check the wall clock only rarely: the check (and the one-time env read
        // behind `stall_budget`) must not slow ordinary contention.
        if spins & 0x3F_FFFF == 0 {
            let budget = stall_budget();
            if !budget.is_zero() {
                let dl = *deadline.get_or_insert_with(|| Instant::now() + budget);
                if Instant::now() >= dl {
                    stall_fail(obj);
                }
            }
        }
        std::hint::spin_loop();
    }
    push_lock_depth(obj);
}

/// Release a cown's lock. Only the outermost release (depth returning to zero)
/// actually frees the spinlock byte; inner releases of a reentrant acquisition
/// just decrement the depth.
///
/// # Safety
/// `obj` must be a valid object header (or null).
pub unsafe extern "C-unwind" fn pp_unlock(obj: *mut Header) {
    if obj.is_null() {
        return;
    }
    if pop_lock_depth(obj) == 0 {
        unsafe { lock_byte(obj) }.store(0, Ordering::Release);
    }
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

/// The cown pointers in a raw `(ptr, n)` span, address-sorted and de-duplicated
/// -- the same global lock order [`array_cowns`] gives an array, for callers
/// (the auto-acquire pass's group wrap) that have the cowns as individual typed
/// values on the stack rather than in a heap array.
unsafe fn span_cowns(ptrs: *const *mut Header, n: i64) -> Vec<*mut Header> {
    if ptrs.is_null() || n <= 0 {
        return Vec::new();
    }
    let mut v: Vec<*mut Header> = (0..n)
        .map(|i| unsafe { *ptrs.offset(i as isize) })
        .collect();
    v.sort_unstable_by_key(|p| *p as usize);
    v.dedup();
    v
}

/// Acquire every cown in a raw pointer span, in address order, so any two group
/// acquisitions of overlapping cown sets use one global lock order and cannot
/// deadlock -- regardless of the textual order the compiler emitted the span in.
///
/// # Safety
/// `ptrs` must point to `n` readable object-header pointers (each valid or null).
pub unsafe extern "C-unwind" fn pp_lock_span(ptrs: *const *mut Header, n: i64) {
    unsafe {
        for p in span_cowns(ptrs, n) {
            pp_lock(p);
        }
    }
}

/// Release every cown in a raw pointer span (reverse acquisition order).
///
/// # Safety
/// `ptrs` must point to `n` readable object-header pointers (each valid or null).
pub unsafe extern "C-unwind" fn pp_unlock_span(ptrs: *const *mut Header, n: i64) {
    unsafe {
        for p in span_cowns(ptrs, n).into_iter().rev() {
            pp_unlock(p);
        }
    }
}

/// Spawn a closure on a new OS thread. The closure is the
/// `{ header | fn-ptr@16 | captures... }` object the typed back end builds; a
/// zero-argument closure's compiled signature is `void(env)`, so the thread calls
/// the function pointer with the closure object as its environment.
///
/// # Safety
/// `closure` must be a closure object as laid out by the typed back end (a
/// function pointer at offset 16 and a destructor pointer -- or 0 -- at offset
/// 24), whose reachable captures the ownership analysis has made safe to hand to
/// another thread (moved, frozen, or cowned).
pub unsafe extern "C-unwind" fn pp_spawn(closure: *mut Header) {
    let captured = SendPtr(closure);
    // Mark a spawn active before the thread starts and clear it only after the
    // thread's last heap operation, so the cycle collector defers while it runs.
    ACTIVE_SPAWNS.fetch_add(1, Ordering::SeqCst);
    let handle = std::thread::spawn(move || {
        // Balance the counter on *every* exit path of the thread body. The body
        // is not supposed to unwind in a real program (runtime errors exit the
        // process), but a test/embedding diagnostic can panic through it; a lost
        // decrement would keep `has_active_spawns()` true forever and silently
        // disable cycle collection for the rest of the process.
        struct SpawnDone;
        impl Drop for SpawnDone {
            fn drop(&mut self) {
                ACTIVE_SPAWNS.fetch_sub(1, Ordering::SeqCst);
            }
        }
        let _done = SpawnDone;
        // Bind the whole `SendPtr` so the closure captures it (which is `Send`),
        // not its raw pointer field (disjoint capture would not be `Send`).
        let captured = captured;
        let env = captured.0;
        unsafe {
            let fnptr = *((env as *mut u8).add(16) as *mut usize);
            // "C-unwind" matches the convention the bodies are compiled with, so
            // an unwinding body propagates as a panic (caught by the join) rather
            // than aborting the process at this frame. An unwound body skips its
            // destructor: the environment leaks, which is sound (never freed twice).
            let f: extern "C-unwind" fn(*mut Header) = std::mem::transmute(fnptr);
            f(env);
            // The spawner moved the closure to this thread (its reference, not a
            // retained copy). Release it via its stored destructor (offset 24),
            // which releases the captures and frees the environment.
            let dtor_ptr = *((env as *mut u8).add(24) as *mut usize);
            if dtor_ptr != 0 {
                let dtor: extern "C-unwind" fn(*mut Header) = std::mem::transmute(dtor_ptr);
                dtor(env);
            }
        }
    });
    threads().lock().unwrap().push(handle);
}

/// Join every spawned thread. The driver calls this in `main`'s epilogue so the
/// program waits for spawned work before exiting. With all threads joined the main
/// thread is again the sole mutator, so it runs a collection to reclaim any cycle
/// garbage whose collection was deferred while spawned threads ran.
///
/// A joined thread that terminated by unwinding (possible only in test/embedding
/// runs; a real program's runtime errors exit the process) is not silently
/// discarded: after every thread is joined, the first failure's payload is
/// re-raised on the joining thread so a failed spawned task surfaces instead of
/// being lost.
pub extern "C-unwind" fn pp_join_all() {
    // A spawned task may itself call `sync()`, and the global registry then
    // contains the *calling thread's own* handle. Joining it would be a self-join
    // -- pthread_join(self) fails with EDEADLK and the std join panics, aborting
    // the program -- so the caller's handle is set aside and handed back to the
    // registry for an enclosing join (ultimately main's epilogue) to drain.
    let me = std::thread::current().id();
    let mut failure: Option<Box<dyn std::any::Any + Send>> = None;
    // A spawned thread may itself spawn (a nested/late spawn), pushing a new handle
    // after this drain started. Loop until the registry holds nothing but the
    // caller's own handle: each round joins the threads taken so far, during which
    // any of them may have pushed more. Without this, a nested spawn is never
    // joined -- its work is lost and it runs into process teardown, a
    // use-after-free of runtime state.
    loop {
        let taken: Vec<_> = std::mem::take(&mut *threads().lock().unwrap());
        let (own, others): (Vec<_>, Vec<_>) =
            taken.into_iter().partition(|h| h.thread().id() == me);
        if !own.is_empty() {
            threads().lock().unwrap().extend(own);
        }
        if others.is_empty() {
            break;
        }
        for h in others {
            if let Err(payload) = h.join() {
                // Keep joining the remaining threads (so none leak into process
                // teardown), then surface the first failure below.
                failure.get_or_insert(payload);
            }
        }
    }
    if let Some(payload) = failure {
        std::panic::resume_unwind(payload);
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
            unsafe { pp_spawn(clo) };
        }
        pp_join_all();

        assert_eq!(
            unsafe { *field(counter) },
            THREADS * PER_THREAD,
            "every increment must survive: no lost updates under contention"
        );
    }

    #[test]
    fn lock_is_reentrant_within_one_thread() {
        // A thread that already holds a cown can acquire it again (a nested `with`
        // on the same cown) without deadlocking against the non-recursive spinlock
        // byte; the byte is released only when the outermost acquisition is. After
        // a balanced nested lock/unlock the byte is free for another acquirer.
        let _serial = serial_spawn();
        let obj = alloc_counter();
        unsafe { *field(obj) = 0 };

        unsafe { pp_lock(obj) };
        unsafe { pp_lock(obj) }; // re-entry: must return, not spin
        unsafe { pp_lock(obj) };
        // Innermost releases keep the lock held by this thread.
        unsafe { pp_unlock(obj) };
        unsafe { pp_unlock(obj) };
        assert_eq!(
            unsafe { lock_byte(obj) }.load(Ordering::Relaxed),
            1,
            "the byte stays held while an outer acquisition remains"
        );
        // Outermost release frees the byte.
        unsafe { pp_unlock(obj) };
        assert_eq!(
            unsafe { lock_byte(obj) }.load(Ordering::Relaxed),
            0,
            "the outermost release frees the lock"
        );
    }

    #[test]
    fn reentrant_acquire_still_excludes_other_threads() {
        // Reentrancy must not weaken cross-thread mutual exclusion: each spawned
        // closure acquires the cown, then re-acquires it (a nested `with`),
        // read-modify-writes the counter, and releases both. No increment may be
        // lost despite the inner re-entry.
        let _serial = serial_spawn();
        let counter = alloc_counter();
        unsafe { *field(counter) = 0 };

        const THREADS: i64 = 8;
        const PER_THREAD: i64 = 5000;

        extern "C" fn work(env: *mut Header) {
            let counter = unsafe { *((env as *mut u8).add(32) as *mut *mut Header) };
            for _ in 0..PER_THREAD {
                unsafe { pp_lock(counter) };
                unsafe { pp_lock(counter) }; // nested re-entry on the same cown
                unsafe {
                    let f = field(counter);
                    *f += 1;
                }
                unsafe { pp_unlock(counter) };
                unsafe { pp_unlock(counter) };
            }
        }

        for _ in 0..THREADS {
            let clo = unsafe { pp_obj_alloc(40) as *mut Header };
            unsafe {
                *((clo as *mut u8).add(16) as *mut usize) = work as *const () as usize;
                *((clo as *mut u8).add(32) as *mut *mut Header) = counter;
            }
            unsafe { pp_spawn(clo) };
        }
        pp_join_all();

        assert_eq!(
            unsafe { *field(counter) },
            THREADS * PER_THREAD,
            "reentrancy must not lose updates across threads"
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
            unsafe { pp_spawn(clo) };
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
            unsafe { pp_spawn(clo) };
        }

        let clo = unsafe { pp_obj_alloc(32) as *mut Header };
        unsafe { *((clo as *mut u8).add(16) as *mut usize) = parent as *const () as usize };
        unsafe { pp_spawn(clo) };
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
            unsafe { pp_spawn(clo) };
        }
        pp_join_all();

        // Both threads ran to completion (no deadlock) and every increment landed.
        assert_eq!(unsafe { *field(a) }, 2 * PER_THREAD);
        assert_eq!(unsafe { *field(b) }, 2 * PER_THREAD);
    }

    #[test]
    fn join_all_from_a_spawned_task_skips_its_own_handle() {
        // A spawned task that calls `sync()` (pp_join_all) finds its *own* handle
        // in the global registry. It must be skipped, not joined: a self-join
        // fails with EDEADLK and the std join panics, which aborted the whole
        // program. After the fix the task's sync returns (joining only siblings)
        // and main's outer join still reaps the task itself.
        let _serial = serial_spawn();
        static RAN: AtomicI64 = AtomicI64::new(0);
        RAN.store(0, Ordering::SeqCst);

        extern "C" fn sibling(_env: *mut Header) {
            RAN.fetch_add(1, Ordering::SeqCst);
        }
        extern "C" fn syncer(_env: *mut Header) {
            // Spawn a sibling and join it from inside this spawned thread; the
            // registry also holds this thread's own handle at this point.
            let clo = unsafe { pp_obj_alloc(32) as *mut Header };
            unsafe { *((clo as *mut u8).add(16) as *mut usize) = sibling as *const () as usize };
            unsafe { pp_spawn(clo) };
            pp_join_all();
            // The sibling's effect is visible after the inner join.
            assert_eq!(RAN.load(Ordering::SeqCst), 1);
            RAN.fetch_add(1, Ordering::SeqCst);
        }

        let clo = unsafe { pp_obj_alloc(32) as *mut Header };
        unsafe { *((clo as *mut u8).add(16) as *mut usize) = syncer as *const () as usize };
        unsafe { pp_spawn(clo) };
        pp_join_all();
        assert_eq!(
            RAN.load(Ordering::SeqCst),
            2,
            "both the sibling and the syncing task ran to completion"
        );
    }

    #[test]
    fn contended_lock_past_stall_budget_fails_loudly() {
        // A lock held forever by one thread must not make a contender hang
        // silently: after the stall budget the contender fails with the
        // suspected-deadlock diagnostic (a panic under test builds). This pins
        // the loud-failure path for genuine lock-order-inversion deadlocks.
        let _serial = serial_spawn();
        let obj = alloc_counter();
        unsafe { pp_lock(obj) };
        // Shrink the budget to 1s so the test is quick; restore afterwards.
        STALL_SECS_PLUS_ONE.store(2, Ordering::Relaxed);
        let addr = obj as usize;
        let contender = std::thread::spawn(move || {
            unsafe { pp_lock(addr as *mut Header) };
        });
        let result = contender.join();
        STALL_SECS_PLUS_ONE.store(0, Ordering::Relaxed);
        unsafe { pp_unlock(obj) };
        assert!(
            result.is_err(),
            "the contender must fail loudly instead of spinning forever"
        );
    }

    #[test]
    fn lock_span_orders_and_dedups() {
        // The span form used by the compiler's group wrap must behave like the
        // array form: lock every distinct cown (duplicates once) and release them
        // all, regardless of the textual order in the span.
        let _serial = serial_spawn();
        let a = alloc_counter();
        let b = alloc_counter();
        let span = [b, a, b];
        unsafe { pp_lock_span(span.as_ptr(), 3) };
        assert_eq!(unsafe { lock_byte(a) }.load(Ordering::Relaxed), 1);
        assert_eq!(unsafe { lock_byte(b) }.load(Ordering::Relaxed), 1);
        unsafe { pp_unlock_span(span.as_ptr(), 3) };
        assert_eq!(unsafe { lock_byte(a) }.load(Ordering::Relaxed), 0);
        assert_eq!(unsafe { lock_byte(b) }.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn lock_span_is_deadlock_free_across_orders() {
        // Two threads group-acquire the same two cowns via spans in opposite
        // orders. Address-sorted acquisition gives one global order, so both
        // finish and no increment is lost (the whole point of replacing the
        // name-ordered nested `with` wrap).
        let _serial = serial_spawn();
        let a = alloc_counter();
        let b = alloc_counter();
        unsafe {
            *field(a) = 0;
            *field(b) = 0;
        }
        const PER_THREAD: i64 = 4000;
        // Closure env: `{ header | fn@16 | dtor@24 (zero) | a@32 | b@40 }`; the
        // worker group-locks (a, b) in its captured order each iteration.
        extern "C" fn work(env: *mut Header) {
            let x = unsafe { *((env as *mut u8).add(32) as *mut *mut Header) };
            let y = unsafe { *((env as *mut u8).add(40) as *mut *mut Header) };
            let span = [x, y];
            for _ in 0..PER_THREAD {
                unsafe { pp_lock_span(span.as_ptr(), 2) };
                unsafe {
                    *field(x) += 1;
                    *field(y) += 1;
                }
                unsafe { pp_unlock_span(span.as_ptr(), 2) };
            }
        }
        for (x, y) in [(a, b), (b, a)] {
            let clo = unsafe { pp_obj_alloc(48) as *mut Header };
            unsafe {
                *((clo as *mut u8).add(16) as *mut usize) = work as *const () as usize;
                *((clo as *mut u8).add(32) as *mut *mut Header) = x;
                *((clo as *mut u8).add(40) as *mut *mut Header) = y;
            }
            unsafe { pp_spawn(clo) };
        }
        pp_join_all();
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

    #[test]
    fn unwinding_spawned_body_balances_active_spawns_and_surfaces() {
        // A spawned body that unwinds (possible in test/embedding runs; a real
        // program's runtime errors exit the process) must still balance
        // ACTIVE_SPAWNS -- a lost decrement would keep `has_active_spawns()`
        // true forever and silently disable cycle collection -- and its failure
        // must surface from `pp_join_all` instead of being discarded.
        let _serial = serial_spawn();

        extern "C-unwind" fn boom(_env: *mut Header) {
            panic!("spawned body failed");
        }

        // `{ header(16) | fn@16 | dtor@24 (zero) }`; the unwound body never
        // reaches its destructor, so the environment intentionally leaks.
        let clo = unsafe { pp_obj_alloc(32) as *mut Header };
        unsafe { *((clo as *mut u8).add(16) as *mut usize) = boom as *const () as usize };
        unsafe { pp_spawn(clo) };

        let joined = std::panic::catch_unwind(|| pp_join_all());
        assert!(
            joined.is_err(),
            "the spawned task's failure must surface from the join"
        );
        assert!(
            !has_active_spawns(),
            "the counter must be balanced even when the body unwinds"
        );
    }
}
