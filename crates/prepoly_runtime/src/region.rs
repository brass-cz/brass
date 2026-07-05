//! Region metadata, the write barrier, and closedness verification. A region is the object subgraph owned by a `with` scope; its bridge
//! is the object `with` guards. Each region tracks a *local reference count* (LRC):
//! the number of references into the region from outside it, plus its bridge owner.
//! A region is **closed** when only its bridge owner references it (LRC == 1) --
//! nothing escaped.
//!
//! Regions form a tree through `parent` links: a region may be
//! nested inside another. A borrow reaching into a child region also reaches into
//! its ancestors, so the first external borrow of a child propagates a borrow up
//! the parent chain, and dropping the last child borrow propagates the release back
//! up. This lets the whole nested tree's closedness be read from a
//! single region's LRC.
//!
//! This is an additive layer over the per-object cown lock that already provides
//! data-race-freedom: regions add ownership *metadata* and a *closedness* check,
//! they do not replace the lock, so soundness is preserved. An object's region id
//! lives in the otherwise-unused `nchild` header slot (0 = not in a region).

use std::collections::BTreeMap;
use std::sync::Mutex;

use crate::rt::{Header, OWNER_BRIDGE, OWNER_CONTAINED, OWNER_IMMUTABLE, OWNER_LOCAL, is_shared};

/// Per-region metadata. `lrc` includes the bridge's own external owner, so it
/// starts at 1 and a region is closed at `lrc == 1` (no other reference in).
/// `parent` is the id of the enclosing region, or 0 at the top level. `bridge` and
/// `prev_owner` record the bridge object and the owner class it had before the
/// region re-tagged it `BRIDGE`, so close can restore it -- otherwise a cown stays
/// `BRIDGE` after its first `with` and is no longer recognised as shared.
struct RegionMeta {
    lrc: i64,
    parent: i64,
    bridge: usize,
    prev_owner: u8,
}

/// Live regions by id, plus the next id to hand out. A region is inserted on
/// `with` entry and removed on close ([`pp_region_close`]), so the table is bounded
/// by the number of *currently open* regions rather than growing once per `with`
/// for the program's lifetime. Ids are monotonic and never reused: an object still
/// carrying a closed region's id in its `nchild` slot can never alias a different,
/// live region; [`live_region_of`] resolves such a stale id to "no region" and
/// lazily restores the header, so the object behaves as region-less again (and can
/// be adopted by a later region) instead of being written into a dead region.
struct RegionTable {
    regions: BTreeMap<i64, RegionMeta>,
    next_id: i64,
}

/// Region table. Guarded for the barrier's updates; a `with` body runs
/// synchronously, so a single region sees little contention.
static REGIONS: Mutex<RegionTable> = Mutex::new(RegionTable {
    regions: BTreeMap::new(),
    next_id: 1,
});

/// Open a top-level region with `bridge` as its entry object; see
/// [`pp_region_open_nested`].
///
/// # Safety
/// `bridge` must be a valid object header (or null).
pub unsafe extern "C-unwind" fn pp_region_open(bridge: *mut Header) -> i64 {
    unsafe { pp_region_open_nested(bridge, 0) }
}

/// Open a region with `bridge` as its entry object, nested inside region `parent`
/// (0 for a top-level region), and return its 1-based id. The bridge -- and objects
/// transferred in by the write barrier -- carry the id in `nchild`. The LRC starts
/// at 1 (the bridge's external owner).
///
/// # Safety
/// `bridge` must be a valid object header (or null).
pub unsafe extern "C-unwind" fn pp_region_open_nested(bridge: *mut Header, parent: i64) -> i64 {
    unsafe {
        let prev_owner = if bridge.is_null() {
            OWNER_LOCAL
        } else {
            (*bridge).owner
        };
        let mut table = REGIONS.lock().unwrap();
        let id = table.next_id;
        table.next_id += 1;
        table.regions.insert(
            id,
            RegionMeta {
                lrc: 1,
                parent,
                bridge: bridge as usize,
                prev_owner,
            },
        );
        if !bridge.is_null() {
            (*bridge).nchild = id as i32;
            // The bridge is the region's single external entry point.
            (*bridge).owner = OWNER_BRIDGE;
        }
        id
    }
}

/// Record a borrow reaching into region `id`: raise its LRC, and
/// when that is the region's *first* external borrow (LRC 1 -> 2), the borrow also
/// reaches the parent, so recurse. `regions` is the already-held table guard.
fn add_borrow(regions: &mut BTreeMap<i64, RegionMeta>, id: i64) {
    let Some(meta) = regions.get_mut(&id) else {
        return;
    };
    meta.lrc += 1;
    let parent = meta.parent;
    if meta.lrc == 2 && parent != 0 {
        add_borrow(regions, parent);
    }
}

/// Drop a borrow into region `id`: lower its LRC, and when that
/// removes the region's *last* external borrow (LRC 2 -> 1), recurse to the parent.
fn remove_borrow(regions: &mut BTreeMap<i64, RegionMeta>, id: i64) {
    let Some(meta) = regions.get_mut(&id) else {
        return;
    };
    if meta.lrc <= 1 {
        return; // already closed: nothing borrowed to drop
    }
    meta.lrc -= 1;
    let parent = meta.parent;
    if meta.lrc == 1 && parent != 0 {
        remove_borrow(regions, parent);
    }
}

/// The *live* region id an object belongs to, or 0 for a region-less (local)
/// object. An object may still carry the id of a region that has since closed
/// (close cannot rewrite its members' headers -- it does not know the member
/// graph); such a stale id resolves to "no region" here, and the header is
/// lazily restored (id cleared, a `Contained` owner back to `Local`) so the
/// object is a plain local again: it can be adopted by a live region instead of
/// being written into a dead one. `regions` is the already-held table guard, so
/// the resolution and the caller's bookkeeping are atomic.
unsafe fn live_region_of(regions: &BTreeMap<i64, RegionMeta>, obj: *mut Header) -> i64 {
    unsafe {
        if obj.is_null() {
            return 0;
        }
        let id = (*obj).nchild as i64;
        if id == 0 || regions.contains_key(&id) {
            return id;
        }
        // Stale: the region closed. `Contained` only ever replaced `Local` (a
        // shared owner never enters a region as an interior element), so `Local`
        // is the correct restoration; a closed bridge's owner was already
        // restored by `pp_region_close`.
        (*obj).nchild = 0;
        if (*obj).owner == OWNER_CONTAINED {
            (*obj).owner = OWNER_LOCAL;
        }
        0
    }
}

/// `_addReference`: account for a new reference `src.field = tgt`
/// against the region model, applying the §12.4 reference rules. This maintains
/// region *membership* and the local reference count; the per-object reference
/// count itself is maintained by the typed back end's retain/release (§8.2), so
/// this does not touch `rc` except where the design folds a borrow into membership.
///
/// # Safety
/// `src`/`tgt` must be valid object headers (or null).
pub unsafe extern "C-unwind" fn pp_add_reference(src: *mut Header, tgt: *mut Header) {
    unsafe {
        if tgt.is_null() {
            return;
        }
        // One guard across resolution and bookkeeping: a stale id must not be
        // resolved against one table state and acted on against another.
        let mut table = REGIONS.lock().unwrap();
        let sr = live_region_of(&table.regions, src);
        let tr = live_region_of(&table.regions, tgt);

        // Same region: an internal reference, no region bookkeeping (fast path -- `_sameRegion`).
        if sr != 0 && sr == tr {
            return;
        }
        // tgt is shared (immutable/cown): freely referenced from anywhere; its own
        // atomic rc (maintained by the back end) is all that is needed.
        if is_shared((*tgt).owner) {
            return;
        }
        // src is local and tgt lives in another region: an external borrow into tr,
        // tracked by the LRC (propagated up the region tree).
        if sr == 0 {
            if tr != 0 {
                add_borrow(&mut table.regions, tr);
            }
            return;
        }
        // Otherwise src owns a region and tgt is region-less: transfer tgt into src's
        // region as a Contained interior element ("->move").
        if tr == 0 {
            (*tgt).nchild = sr as i32;
            (*tgt).owner = OWNER_CONTAINED;
        } else {
            // tgt is in a different region than src: an external borrow into tr.
            add_borrow(&mut table.regions, tr);
        }
    }
}

/// `_removeReference`: account for the removal of the old value of
/// a field. If `old` was an external borrow from `src` into another region, drop
/// that borrow so the target region can become closed again.
///
/// # Safety
/// `src`/`old` must be valid object headers (or null).
pub unsafe extern "C-unwind" fn pp_remove_reference(src: *mut Header, old: *mut Header) {
    unsafe {
        if old.is_null() {
            return;
        }
        let mut table = REGIONS.lock().unwrap();
        let sr = live_region_of(&table.regions, src);
        let or = live_region_of(&table.regions, old);
        // An external borrow existed only when `old` was in a different region than
        // `src` (and `src` did not share `old`'s region). Drop it.
        if or != 0 && or != sr {
            remove_borrow(&mut table.regions, or);
        }
    }
}

/// The full write barrier `_writeBarrier(src, old, tgt)`: reject
/// writes through an immutable or cown handle, add the new reference, and remove
/// the old one. Inserted by the typed back end on a field store `src.f = tgt` whose
/// previous value was `old`.
///
/// # Safety
/// `src`/`old`/`tgt` must be valid object headers (or null).
pub unsafe extern "C-unwind" fn pp_write_barrier(
    src: *mut Header,
    old: *mut Header,
    tgt: *mut Header,
) {
    unsafe {
        // 1. A write through an immutable or cown handle is illegal:
        //    Immutable is read-only; a cown's interior is reached only by acquiring it,
        //    not by writing the cown cell itself.
        if !src.is_null() && is_shared((*src).owner) {
            crate::builtins::pp_panic_str("cannot write to immutable or cown object");
        }
        // 2/3. Add the new reference, remove the old.
        pp_add_reference(src, tgt);
        pp_remove_reference(src, old);
    }
}

/// Reject a store into a deeply frozen object. Freezing promises every thread
/// that the object graph will never change again -- readers access it without any
/// lock -- so a write through a frozen handle is a data race by construction.
/// Failing loudly here turns a silent race into a defined error. Under unit tests
/// this panics (unwinds) so the rejection is observable in-process; in a real
/// program it exits through the runtime error path.
fn reject_frozen_write() -> ! {
    let msg = "cannot write to a frozen (immutable) object: it is shared lock-free \
               across threads";
    #[cfg(test)]
    panic!("{msg}");
    #[cfg(not(test))]
    crate::builtins::pp_panic_str(msg)
}

/// Reduced write barrier retained for the typed back end's current field-store
/// path: same as [`pp_add_reference`] but also performs the local-value
/// transfer used when no `src` owner is known. `src` is the container, `value` the
/// stored value; equivalent to `pp_add_reference` with the container as `src`.
///
/// A store whose container is *frozen* (deeply immutable, shared lock-free across
/// threads) is rejected loudly: see [`reject_frozen_write`]. A cown container is
/// legal here -- the back end emits this barrier for stores it performs under the
/// cown's lock (a group-acquired `with` leaves the owner tag as `Cown`).
///
/// # Safety
/// `container`/`value` must be valid object headers (or null).
pub unsafe extern "C-unwind" fn pp_region_write(container: *mut Header, value: *mut Header) {
    unsafe {
        if !container.is_null() && (*container).owner == OWNER_IMMUTABLE {
            reject_frozen_write();
        }
        pp_add_reference(container, value);
    }
}

/// The heap value held by a nullable cell `{ header16 | value@16 }`, or null for
/// an absent cell. Only meaningful when the cell's content is a managed pointer
/// (the caller's `managed_cells` flag).
unsafe fn cell_content(cell: *mut Header) -> *mut Header {
    unsafe {
        if cell.is_null() {
            std::ptr::null_mut()
        } else {
            *((cell as *mut u8).add(16) as *mut *mut Header)
        }
    }
}

/// The typed back end's full store barrier for an overwriting store
/// `container.f = value` whose previous value was `old`: reject a write into a
/// frozen container, account the new reference, and drop the old one. This is
/// [`pp_write_barrier`] with [`pp_region_write`]'s container rule -- a *cown*
/// container is legal because the back end emits this barrier only for stores it
/// performs under the cown's lock (a `with`-acquired bridge or group member) --
/// so escaped references are counted *and* un-counted symmetrically: without the
/// old-reference removal, an overwritten escape would keep a region open forever.
///
/// `managed_cells != 0` says the slot is a nullable whose content is itself a
/// managed pointer: `old`/`value` are then cells wrapping a separately tracked
/// object, and that content is accounted exactly like the cell -- otherwise a
/// region member stored through a `T?` slot would raise the borrow on the way in
/// (or join the region) with no matching drop when the slot is overwritten.
///
/// # Safety
/// `container`/`old`/`value` must be valid object headers (or null); when
/// `managed_cells != 0`, `old` and `value` must be nullable cells whose value
/// slot holds an object header (or null).
pub unsafe extern "C-unwind" fn pp_region_store(
    container: *mut Header,
    old: *mut Header,
    value: *mut Header,
    managed_cells: i64,
) {
    unsafe {
        if !container.is_null() && (*container).owner == OWNER_IMMUTABLE {
            reject_frozen_write();
        }
        pp_add_reference(container, value);
        if managed_cells != 0 {
            pp_add_reference(container, cell_content(value));
        }
        // Drop the old references only after the new ones are counted, so an
        // old == value re-store never dips a borrow to zero in between.
        if managed_cells != 0 {
            pp_remove_reference(container, cell_content(old));
        }
        pp_remove_reference(container, old);
    }
}

/// Drop an external borrow into region `id`: the inverse of the
/// escape recorded by [`pp_add_reference`], used when an escaping reference is later
/// released (a removed reference in the write barrier, §12.5). Propagates up the
/// region tree.
pub extern "C-unwind" fn pp_region_unborrow(id: i64) {
    if id <= 0 {
        return;
    }
    remove_borrow(&mut REGIONS.lock().unwrap().regions, id);
}

/// Closedness verification on region release: a region is
/// closed iff only its bridge owner references it (LRC == 1) -- i.e. no reference
/// into it (or, by parent propagation, into any descendant) escaped during the
/// `with` scope. Returns true when closed.
pub extern "C-unwind" fn pp_region_close(id: i64) -> bool {
    if id <= 0 {
        return true;
    }
    // The `with` scope is ending: drop the region's metadata (ids are monotonic and
    // never reused, so this bounds the table to open regions without letting a stale
    // `nchild` later alias a different live region) and restore the bridge's owner
    // class so a cown is recognised as shared again after the scope.
    let Some(meta) = REGIONS.lock().unwrap().regions.remove(&id) else {
        return true;
    };
    if meta.bridge != 0 {
        unsafe {
            (*(meta.bridge as *mut Header)).owner = meta.prev_owner;
        }
    }
    meta.lrc == 1
}

/// Non-destructive closedness query for tests, which check a region's closedness
/// at several points during its life (the runtime's `pp_region_close` is called
/// once, at scope exit, and disposes the region).
#[cfg(test)]
fn region_is_closed(id: i64) -> bool {
    REGIONS
        .lock()
        .unwrap()
        .regions
        .get(&id)
        .is_none_or(|meta| meta.lrc == 1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alloc::pp_typed_alloc;
    use std::sync::MutexGuard;

    /// These tests allocate through the shared counted heap. Hold the crate's
    /// heap-test lock so the tests elsewhere that assert on `pp_live_blocks`
    /// (gc, conc) never observe this module's allocations mid-flight.
    fn serial_region() -> MutexGuard<'static, ()> {
        crate::serial_heap_test()
    }

    /// A region with no escape stays closed; an external reference into it (the
    /// write barrier raising the LRC) makes it not closed.
    #[test]
    fn closedness_tracks_escapes() {
        let _serial = serial_region();
        unsafe {
            let bridge = pp_typed_alloc(32);
            let inner = pp_typed_alloc(16);
            let id = pp_region_open(bridge);
            // Store `inner` into the region's bridge: `inner` joins the region.
            pp_region_write(bridge, inner);
            assert_eq!((*inner).nchild, id as i32, "inner transferred into region");
            assert!(region_is_closed(id), "no escape -> closed");

            // Now make `inner` reachable from an external (region-less) object: an
            // escape raises the LRC, so the region is no longer closed.
            let outside = pp_typed_alloc(16);
            pp_region_write(outside, inner);
            assert!(!region_is_closed(id), "escaped reference -> not closed");
        }
    }

    /// A borrow into a nested child region propagates up: it opens the parent too,
    /// and dropping the borrow closes both again (LRC).
    #[test]
    fn nested_lrc_propagates_to_parent() {
        let _serial = serial_region();
        unsafe {
            let parent_bridge = pp_typed_alloc(16);
            let child_bridge = pp_typed_alloc(32);
            let child_inner = pp_typed_alloc(16);

            let parent = pp_region_open(parent_bridge);
            let child = pp_region_open_nested(child_bridge, parent);
            // Put an object into the child region.
            pp_region_write(child_bridge, child_inner);
            assert!(region_is_closed(parent), "no borrows yet -> parent closed");
            assert!(region_is_closed(child), "no borrows yet -> child closed");

            // An external object borrows into the child: the child opens, and the
            // borrow also reaches the parent, so the parent opens too.
            let outside = pp_typed_alloc(16);
            pp_region_write(outside, child_inner);
            assert!(!region_is_closed(child), "borrow into child -> child open");
            assert!(
                !region_is_closed(parent),
                "borrow into child reaches parent -> parent open"
            );

            // Dropping the borrow closes the child, which propagates up and closes
            // the parent.
            pp_region_unborrow(child);
            assert!(region_is_closed(child), "borrow dropped -> child closed");
            assert!(
                region_is_closed(parent),
                "last child borrow dropped -> parent closed"
            );
        }
    }

    /// The full write barrier's add/remove pair: storing a region
    /// object into an external container opens its region (an escape borrow); later
    /// overwriting that field (removing the old reference) closes it again.
    #[test]
    fn write_barrier_add_then_remove_reference() {
        let _serial = serial_region();
        unsafe {
            let bridge = pp_typed_alloc(16);
            let inner = pp_typed_alloc(16);
            let id = pp_region_open(bridge);
            pp_add_reference(bridge, inner); // inner joins the region (Contained)
            assert!(region_is_closed(id), "no escape yet");

            // An external container references `inner`: the region opens.
            let container = pp_typed_alloc(24);
            pp_write_barrier(container, std::ptr::null_mut(), inner);
            assert!(!region_is_closed(id), "escape borrow -> open");

            // The container's field is overwritten, dropping the old reference to
            // `inner`: the borrow is released and the region closes.
            pp_write_barrier(container, inner, std::ptr::null_mut());
            assert!(region_is_closed(id), "old reference removed -> closed");
        }
    }

    /// A store whose container is frozen (deeply immutable) is rejected loudly:
    /// frozen objects are read lock-free from any thread, so a write is a data
    /// race by construction and must not proceed silently.
    #[test]
    fn store_into_a_frozen_container_is_rejected() {
        let _serial = serial_region();
        unsafe {
            let container = pp_typed_alloc(24);
            let value = pp_typed_alloc(16);
            (*container).owner = crate::rt::OWNER_FROZEN;
            let result = std::panic::catch_unwind(|| {
                pp_region_write(container, value);
            });
            assert!(result.is_err(), "frozen write must fail loudly");
        }
    }

    /// An object still carrying a closed region's id must act as region-less: a
    /// store *through* it must not adopt the value into the dead region, and its
    /// header is lazily restored to the local state.
    #[test]
    fn stale_id_does_not_transfer_into_a_dead_region() {
        let _serial = serial_region();
        unsafe {
            let bridge = pp_typed_alloc(24);
            let inner = pp_typed_alloc(16);
            let id = pp_region_open(bridge);
            pp_region_write(bridge, inner); // inner joins the region
            assert!(pp_region_close(id));

            // `inner` still carries the dead id. Using it as a container must not
            // write a fresh object into the dead region (that object would then
            // carry a dead id and a Contained owner forever).
            let fresh = pp_typed_alloc(16);
            pp_region_write(inner, fresh);
            assert_eq!((*fresh).nchild, 0, "no adoption into a closed region");
            assert_eq!((*fresh).owner, OWNER_LOCAL);
            // The stale header was lazily restored to the region-less state.
            assert_eq!((*inner).nchild, 0, "stale id cleared on first touch");
            assert_eq!((*inner).owner, OWNER_LOCAL, "Contained restored to Local");
        }
    }

    /// A member of a closed region can be adopted by a *later* region, and borrow
    /// accounting against it works again: before the stale-id resolution, the
    /// object kept the dead id, the new region never adopted it, and an external
    /// borrow of it went uncounted (a silent escape).
    #[test]
    fn closed_region_member_rejoins_a_live_region_and_escapes_are_counted() {
        let _serial = serial_region();
        unsafe {
            let first_bridge = pp_typed_alloc(24);
            let obj = pp_typed_alloc(16);
            let first = pp_region_open(first_bridge);
            pp_region_write(first_bridge, obj);
            assert!(pp_region_close(first));

            // A later region adopts the same object on write.
            let second_bridge = pp_typed_alloc(24);
            let second = pp_region_open(second_bridge);
            pp_region_write(second_bridge, obj);
            assert_eq!(
                (*obj).nchild,
                second as i32,
                "the stale member is re-adopted by the live region"
            );

            // An external reference to the re-adopted member is a real escape and
            // must be counted against the live region.
            let outside = pp_typed_alloc(16);
            pp_region_write(outside, obj);
            assert!(
                !pp_region_close(second),
                "the escape through a re-adopted member is detected"
            );
        }
    }

    /// Closing a region disposes its metadata and the id is never reused, so the
    /// table is bounded by the number of open regions rather than growing once per
    /// `with` (the previous unbounded leak).
    #[test]
    fn closing_a_region_disposes_it_with_monotonic_ids() {
        let _serial = serial_region();
        unsafe {
            let id = pp_region_open(pp_typed_alloc(16));
            assert!(pp_region_close(id), "no escape -> closed");
            // The id is gone; querying it now reports "closed" (no entry) and a new
            // region receives a strictly greater id, never the freed one.
            assert!(region_is_closed(id), "disposed region resolves to no entry");
            let id2 = pp_region_open(pp_typed_alloc(16));
            assert!(id2 > id, "ids are monotonic and never reused");
            pp_region_close(id2);
        }
    }
}
