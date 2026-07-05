//! Cycle collector: trial deletion (the Bacon-Rajan algorithm)
//! for reference cycles that plain reference counting (`crate::alloc`) cannot
//! reclaim. A cycle keeps every member's count above zero, so no member is ever
//! freed by `pp_release`; this collector finds such garbage.
//!
//! The runtime cannot itself know an object's outgoing references (the typed back
//! end lays out records/sums), so each cycle-capable object registers a *trace*
//! function at construction (`pp_gc_register`) that visits its managed children.
//! The registry doubles as the collector's candidate set; `pp_gc_collect` runs the
//! trial deletion over it: trial-decrement child counts (mark gray), restore the
//! externally-reachable (scan/scan-black), and free what stays white (a cycle with
//! no outside references).
//!
//! Collection is scheduled generationally: registration advances an
//! allocation counter that triggers a Gen 0 collection every `GEN0_ALLOCS`
//! allocations, with Gen 1/Gen 2 milestones every 10th/100th Gen 0 (see
//! `schedule_tick`). The driver also calls `pp_gc_collect` once before exit to
//! sweep whatever remains.

use std::collections::HashMap;
use std::os::raw::c_void;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

use crate::rt::{Header, OWNER_IMMUTABLE};

/// Count of registered (cycle-capable) live objects, so the allocator's free path
/// can skip the registry lock entirely when there is nothing to collect.
static REGISTERED: AtomicUsize = AtomicUsize::new(0);

// ----- generational collection schedule -----
//
// Cycle-capable allocations are counted; every `gen0_threshold` allocations trigger
// a Gen 0 collection, every 10th Gen 0 is also a Gen 1, and every 10th Gen 1 a Gen
// 2. The registry is unified, so every generation runs the same full trial-deletion
// pass (a full pass is always sound; the tiers are escalating cadences) -- this
// reclaims cycles continuously during a long run instead of only at program exit.

/// Default Gen 0 cadence: one collection per 700 cycle-capable allocations.
const GEN0_ALLOCS: usize = 700;
/// Each higher generation fires once per this many of the generation below it.
const GEN_RATIO: usize = 10;

/// Allocations since the last Gen 0 collection.
static ALLOC_TICKS: AtomicUsize = AtomicUsize::new(0);
/// The Gen 0 cadence; configurable (see `pp_gc_set_gen0_threshold`) for testing.
static GEN0_THRESHOLD: AtomicUsize = AtomicUsize::new(GEN0_ALLOCS);
/// How many Gen 0 collections have run (the index that drives gen escalation).
static GEN0_RUNS: AtomicUsize = AtomicUsize::new(0);
/// Guards against re-entrant/concurrent scheduled collections: only one runs at a
/// time, others skip (the next allocation will reschedule).
static COLLECTING: AtomicBool = AtomicBool::new(false);

/// The highest generation that fires at the `g0`-th Gen 0 collection (1-based):
/// Gen 2 every `GEN_RATIO` Gen 1s (every `GEN_RATIO^2` Gen 0s), Gen 1 every
/// `GEN_RATIO` Gen 0s, else Gen 0. A pure function of the collection index so the
/// schedule is testable without touching the heap.
fn generation_for(g0: usize) -> u8 {
    if g0 != 0 && g0.is_multiple_of(GEN_RATIO * GEN_RATIO) {
        2
    } else if g0 != 0 && g0.is_multiple_of(GEN_RATIO) {
        1
    } else {
        0
    }
}

/// Tick the allocation counter (called once per cycle-capable registration) and run
/// a scheduled collection when the Gen 0 cadence is reached. Returns the generation
/// collected, or `None` if no collection ran this tick.
fn schedule_tick() -> Option<u8> {
    let threshold = GEN0_THRESHOLD.load(Ordering::Relaxed).max(1);
    if ALLOC_TICKS.fetch_add(1, Ordering::Relaxed) + 1 < threshold {
        return None;
    }
    ALLOC_TICKS.store(0, Ordering::Relaxed);
    // `pp_gc_collect` self-serializes: if another collection is already running
    // (a concurrent allocator thread, or a direct call), this one skips and the
    // in-flight collection covers it; reschedule on the next allocation.
    let g0 = GEN0_RUNS.fetch_add(1, Ordering::Relaxed) + 1;
    pp_gc_collect();
    Some(generation_for(g0))
}

/// Set the Gen 0 allocation cadence (number of cycle-capable allocations per Gen 0
/// collection). Intended for tests; production uses the default `GEN0_ALLOCS`.
pub extern "C-unwind" fn pp_gc_set_gen0_threshold(n: i64) {
    GEN0_THRESHOLD.store((n.max(1)) as usize, Ordering::Relaxed);
}

/// The number of Gen 0 collections run so far (for tests/introspection).
pub extern "C-unwind" fn pp_gc_gen0_runs() -> i64 {
    GEN0_RUNS.load(Ordering::Relaxed) as i64
}

// Trial-deletion colors, stored in the object header's `color` byte. `black` is the
// default (in use); a fresh object is black.
const BLACK: u8 = 0; // in use, or already processed this collection
const GRAY: u8 = 1; // under examination (its children's counts were trial-decremented)
const WHITE: u8 = 2; // provisionally garbage (a cycle member with no external reference)

/// A type's child-tracing function: invokes `visit` on each managed (heap) child of
/// `obj`. Emitted per type by the typed back end (mirrors the per-type destructor).
pub type TraceFn = extern "C-unwind" fn(*mut Header, extern "C-unwind" fn(*mut Header));

/// Live cycle-capable objects mapped to their trace function (both as raw
/// addresses). Populated at construction, removed on free; also the collector's
/// candidate set.
fn registry() -> &'static Mutex<HashMap<usize, usize>> {
    static R: OnceLock<Mutex<HashMap<usize, usize>>> = OnceLock::new();
    R.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Objects to free after a collection pass, gathered so freeing never happens while
/// the cycle is still being traversed (which would be a use-after-free).
fn pending_free() -> &'static Mutex<Vec<usize>> {
    static F: OnceLock<Mutex<Vec<usize>>> = OnceLock::new();
    F.get_or_init(|| Mutex::new(Vec::new()))
}

/// Register `obj` (a cycle-capable object) with its trace function. The typed back
/// end calls this right after constructing a record/sum/array/closure.
///
/// # Safety
/// `obj` must be a valid object header (or null) that stays valid until it is
/// freed through [`crate::mem::pp_obj_free`], and `trace` must be the address of
/// a [`TraceFn`] that visits exactly `obj`'s managed children (the collector
/// later transmutes and calls it).
pub unsafe extern "C-unwind" fn pp_gc_register(obj: *mut Header, trace: usize) {
    if !obj.is_null()
        && registry()
            .lock()
            .unwrap()
            .insert(obj as usize, trace)
            .is_none()
    {
        REGISTERED.fetch_add(1, Ordering::Relaxed);
        // Advance the generational schedule; this may run a collection. The registry lock above is released before this point, so the
        // collection it may trigger does not deadlock against registration.
        schedule_tick();
    }
}

/// Drop `obj` from the registry.
pub(crate) fn unregister(obj: *mut Header) {
    if registry().lock().unwrap().remove(&(obj as usize)).is_some() {
        REGISTERED.fetch_sub(1, Ordering::Relaxed);
    }
}

/// The allocator's free path: unregister `obj` if anything is registered. The
/// atomic check keeps a program with no cycle-capable objects off the registry lock.
pub(crate) fn on_free(obj: *mut Header) {
    if REGISTERED.load(Ordering::Relaxed) != 0 {
        unregister(obj);
    }
}

/// The trace function for `obj`, if registered. Looked up and released before the
/// call so a tracer that recurses into the collector does not deadlock.
unsafe fn trace(obj: *mut Header, visit: extern "C-unwind" fn(*mut Header)) {
    unsafe {
        let t = registry().lock().unwrap().get(&(obj as usize)).copied();
        if let Some(t) = t {
            let f: TraceFn = std::mem::transmute(t);
            f(obj, visit);
        }
    }
}

unsafe fn color(h: *mut Header) -> u8 {
    unsafe { (*h).color }
}
unsafe fn set_color(h: *mut Header, c: u8) {
    unsafe {
        (*h).color = c;
    }
}

// ----- the four trial-deletion passes (Bacon-Rajan) -----

unsafe fn mark_gray(h: *mut Header) {
    unsafe {
        if color(h) != GRAY {
            set_color(h, GRAY);
            trace(h, mark_gray_child);
        }
    }
}
extern "C-unwind" fn mark_gray_child(c: *mut Header) {
    if c.is_null() {
        return;
    }
    unsafe {
        (*c).rc -= 1; // trial decrement: remove the internal reference
        mark_gray(c);
    }
}

unsafe fn scan(h: *mut Header) {
    unsafe {
        if color(h) == GRAY {
            if (*h).rc > 0 {
                // Reachable from outside the candidate set: restore it and its subgraph.
                scan_black(h);
            } else {
                set_color(h, WHITE);
                trace(h, scan_child);
            }
        }
    }
}
extern "C-unwind" fn scan_child(c: *mut Header) {
    if c.is_null() {
        return;
    }
    unsafe { scan(c) }
}

unsafe fn scan_black(h: *mut Header) {
    unsafe {
        set_color(h, BLACK);
        trace(h, scan_black_child);
    }
}
extern "C-unwind" fn scan_black_child(c: *mut Header) {
    if c.is_null() {
        return;
    }
    unsafe {
        (*c).rc += 1; // undo the trial decrement
        if color(c) != BLACK {
            scan_black(c);
        }
    }
}

unsafe fn collect_white(h: *mut Header) {
    unsafe {
        if color(h) == WHITE {
            set_color(h, BLACK); // mark processed so the cycle is walked only once
            trace(h, collect_white_child);
            pending_free().lock().unwrap().push(h as usize);
        }
    }
}
extern "C-unwind" fn collect_white_child(c: *mut Header) {
    if c.is_null() {
        return;
    }
    unsafe { collect_white(c) }
}

/// Deeply freeze `obj` and everything it transitively owns:
/// mark each Immutable so its reference count becomes atomic and the subgraph is
/// safely shareable across threads. Children are visited via the same per-type
/// trace function the collector uses; leaf objects (strings, primitive arrays) have
/// no managed children and are frozen in place. The Immutable check short-circuits
/// cycles and already-frozen subgraphs, so this terminates on any object graph.
///
/// # Safety
/// `obj` must be a valid object header (or null).
pub unsafe extern "C-unwind" fn pp_freeze_deep(obj: *mut Header) {
    if obj.is_null() {
        return;
    }
    unsafe {
        if (*obj).owner == OWNER_IMMUTABLE {
            return;
        }
        (*obj).owner = OWNER_IMMUTABLE;
        trace(obj, freeze_child);
    }
}
extern "C-unwind" fn freeze_child(c: *mut Header) {
    unsafe { pp_freeze_deep(c) };
}

/// Run one trial-deletion collection over every registered object. Frees the
/// members of every garbage cycle (reference cycles unreachable from outside).
///
/// Self-serializing: a collection that fires while another is running (a direct
/// call -- e.g. at program exit -- overlapping a scheduled one, or a second
/// allocator thread crossing the threshold) skips, because both share the global
/// registry and pending-free buffer and an overlap would trace or free the same
/// object twice. The in-flight collection already covers the current garbage.
pub extern "C-unwind" fn pp_gc_collect() {
    // Defer collection while any spawned thread is running. The trial-deletion
    // pass mutates every registered object's `rc`/`color` non-atomically and frees
    // the garbage it finds, which would race a concurrent mutator on another
    // thread. With no spawn active the main thread is the sole mutator (and cannot
    // start a spawn while blocked here), so the pass has exclusive access;
    // `pp_join_all` runs a collection once all threads have joined to reclaim what
    // was deferred.
    if crate::conc::has_active_spawns() {
        return;
    }
    if COLLECTING
        .compare_exchange(false, true, Ordering::AcqRel, Ordering::Relaxed)
        .is_err()
    {
        return;
    }
    collect_once();
    COLLECTING.store(false, Ordering::Release);
}

/// One trial-deletion pass over the registry. The caller holds `COLLECTING`.
fn collect_once() {
    let objs: Vec<usize> = registry().lock().unwrap().keys().copied().collect();
    unsafe {
        for &o in &objs {
            mark_gray(o as *mut Header);
        }
        for &o in &objs {
            scan(o as *mut Header);
        }
        for &o in &objs {
            collect_white(o as *mut Header);
        }
    }
    // Free the collected garbage. Unregister first so the allocator's free path does
    // not re-enter the (now stale) registry entry.
    let to_free: Vec<usize> = std::mem::take(&mut *pending_free().lock().unwrap());
    for addr in to_free {
        let h = addr as *mut Header;
        unregister(h);
        unsafe { crate::mem::pp_obj_free(h as *mut c_void) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alloc::{pp_release, pp_typed_alloc};
    use crate::mem::pp_live_blocks;
    use std::sync::MutexGuard;

    /// The schedule (`ALLOC_TICKS`/`GEN0_RUNS`/`GEN0_THRESHOLD`) and the shared
    /// allocator are global, and only these gc tests tick the schedule via
    /// `pp_gc_register`. Each holds this lock so they never run concurrently and
    /// cannot collect each other's garbage at an unexpected moment.
    fn serial_gc() -> MutexGuard<'static, ()> {
        crate::serial_heap_test()
    }

    // A two-field-capable object `{ header16 | child@16: *Header }`; its trace
    // visits the single child pointer.
    extern "C-unwind" fn trace_node(obj: *mut Header, visit: extern "C-unwind" fn(*mut Header)) {
        unsafe {
            let child = *((obj as *mut u8).add(16) as *mut *mut Header);
            if !child.is_null() {
                visit(child);
            }
        }
    }

    unsafe fn node() -> *mut Header {
        unsafe {
            let h = pp_typed_alloc(24);
            (*h).rc = 1;
            *((h as *mut u8).add(16) as *mut *mut Header) = std::ptr::null_mut();
            pp_gc_register(h, trace_node as *const () as usize);
            h
        }
    }

    unsafe fn set_child(obj: *mut Header, child: *mut Header) {
        unsafe {
            *((obj as *mut u8).add(16) as *mut *mut Header) = child;
            (*child).rc += 1; // the field now references `child`
        }
    }

    // A self-cycle (a -> a) and a two-node cycle (a <-> b), once dropped from the
    // program (their external count removed), are reclaimed by the collector even
    // though reference counting alone never frees them.
    #[test]
    fn collects_self_and_two_node_cycles() {
        let _serial = serial_gc();
        unsafe {
            let base = pp_live_blocks();

            // Self-cycle: a.next = a, then drop the local (rc 1 -> 0 via the field's
            // own +1 leaves rc 1, a leak without cycle collection).
            let a = node();
            set_child(a, a);
            (*a).rc -= 1; // the local variable goes out of scope

            // Two-node cycle: a <-> b.
            let x = node();
            let y = node();
            set_child(x, y);
            set_child(y, x);
            (*x).rc -= 1;
            (*y).rc -= 1;

            assert!(
                pp_live_blocks() > base,
                "the cycles leak under plain reference counting"
            );
            pp_gc_collect();
            assert_eq!(
                pp_live_blocks(),
                base,
                "the collector reclaims every cycle member"
            );
        }
    }

    /// `pp_freeze_deep` marks an object and everything it transitively owns
    /// Immutable, following the registered trace; a cycle does not
    /// make it loop forever.
    #[test]
    fn freeze_deep_marks_whole_subgraph() {
        let _serial = serial_gc();
        unsafe {
            let a = node();
            let b = node();
            set_child(a, b); // a -> b
            set_child(b, b); // b -> b (a self-cycle to exercise the cycle guard)

            pp_freeze_deep(a);
            assert_eq!((*a).owner, OWNER_IMMUTABLE, "root frozen");
            assert_eq!(
                (*b).owner,
                OWNER_IMMUTABLE,
                "transitively-owned child frozen"
            );

            // Clean up directly (the nodes form a cycle, so plain rc never frees
            // them): unregister and free both exactly once.
            unregister(a);
            unregister(b);
            crate::mem::pp_obj_free(a as *mut c_void);
            crate::mem::pp_obj_free(b as *mut c_void);
        }
    }

    /// The generation schedule: Gen 1 fires every 10th Gen 0 and
    /// Gen 2 every 10th Gen 1 (every 100th Gen 0); all other Gen 0s are plain.
    #[test]
    fn generation_schedule_escalates() {
        assert_eq!(generation_for(1), 0);
        assert_eq!(generation_for(9), 0);
        assert_eq!(generation_for(10), 1, "every 10th Gen 0 is a Gen 1");
        assert_eq!(generation_for(20), 1);
        assert_eq!(generation_for(99), 0);
        assert_eq!(generation_for(100), 2, "every 100th Gen 0 is a Gen 2");
        assert_eq!(generation_for(200), 2);
        assert_eq!(generation_for(110), 1, "Gen 1 but not Gen 2");
    }

    /// Reaching the Gen 0 allocation threshold auto-triggers a collection mid-run
    /// (not just at program exit): a garbage cycle present in the registry is
    /// reclaimed by the scheduled pass, and the Gen 0 run counter advances.
    #[test]
    fn allocation_threshold_triggers_scheduled_collection() {
        let _serial = serial_gc();
        unsafe {
            let base = pp_live_blocks();
            ALLOC_TICKS.store(0, Ordering::Relaxed);
            let g0_base = pp_gc_gen0_runs();
            pp_gc_set_gen0_threshold(4);

            // A garbage self-cycle: registering `a` is tick 1 (below threshold).
            let a = node();
            set_child(a, a);
            (*a).rc -= 1; // drop the external reference -> garbage

            // Three live dummies (ticks 2, 3, 4); the fourth registration reaches
            // the threshold and runs a Gen 0 collection.
            let keep: Vec<*mut Header> = (0..3).map(|_| node()).collect();

            assert_eq!(
                pp_gc_gen0_runs(),
                g0_base + 1,
                "crossing the threshold ran exactly one Gen 0 collection"
            );
            assert_eq!(
                pp_live_blocks(),
                base + 3,
                "the scheduled collection reclaimed the garbage cycle, kept the dummies"
            );

            // Clean up the dummies so the test is allocation-neutral.
            for d in keep {
                pp_release(d);
            }
            pp_gc_set_gen0_threshold(GEN0_ALLOCS as i64);
            assert_eq!(
                pp_live_blocks(),
                base,
                "test leaves the heap as it found it"
            );
        }
    }
}
