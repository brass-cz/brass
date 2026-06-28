//! Core heap object header shared with the typed JIT-compiled code. Every heap
//! object is prefixed with a 16-byte `Header`; the typed back end lays out the
//! object body itself (strings, arrays, records/sums, Result cells) and accesses
//! the fields directly. The bump allocator that produces these objects lives in
//! `crate::mem`.

// ----- integer / float tags -----
//
// Tags identify the width and signedness of an integer kind (or the float
// width). They are passed to the typed conversion entry points so a runtime
// range check matches the target type.

pub const TAG_INT_I8: i64 = 8;
pub const TAG_INT_I16: i64 = 9;
pub const TAG_INT_I32: i64 = 10;
pub const TAG_INT_I64: i64 = 11;
pub const TAG_INT_U8: i64 = 12;
pub const TAG_INT_U16: i64 = 13;
pub const TAG_INT_U32: i64 = 14;
pub const TAG_INT_U64: i64 = 15;
pub const TAG_F32: i64 = 16;
pub const TAG_F64: i64 = 17;

// ----- object kinds -----

pub const KIND_STRING: u8 = 1;
/// A typed monomorphized heap object laid out by the typed back end itself: its
/// fields are concrete typed values, so nothing traverses them. Strings, arrays,
/// Result cells, and nullable cells the runtime hands back all carry this kind.
pub const KIND_TYPED: u8 = 8;

// ----- owner classes (DESIGN.md 8.1, 12.2) -----
//
// An object's `owner` selects how its reference count behaves and how it may be
// shared across threads, which is the substrate for move/freeze. The five classes
// split into "owned" (exclusive, non-atomic rc) and "shared" (cross-thread, atomic
// rc); the numeric order places the two shared classes last so the atomicity test
// is a single `>=` comparison (see `is_shared`).
//
//   owned (non-atomic rc):
//     Local      thread-local default; auto-moves into a region on cross-region ref
//     Contained  region-interior element; mutable, not referenced from outside
//     Bridge     region entry point; a single unique external reference
//   shared (atomic rc):
//     Immutable  deeply frozen; safely readable from any thread
//     Cown       concurrent cell; reached only under its lock (with-acquire)

/// Thread-local, mutable, non-atomic reference count (the default).
pub const OWNER_LOCAL: u8 = 0;
/// A region's interior element: mutable, never referenced directly from outside.
pub const OWNER_CONTAINED: u8 = 1;
/// A region's entry point (bridge): the single external handle to the region.
pub const OWNER_BRIDGE: u8 = 2;
/// Deeply immutable and shareable across threads; its reference count is atomic.
pub const OWNER_IMMUTABLE: u8 = 3;
/// Owned by a cown; mutated only under the cown's lock; reference count is atomic.
pub const OWNER_COWN: u8 = 4;

/// Back-compat alias: the freeze operation produces `Immutable` objects. The
/// runtime historically named this class "frozen".
pub const OWNER_FROZEN: u8 = OWNER_IMMUTABLE;

/// Whether an owner class is shared across threads, for the region write barrier
/// (`prepoly_runtime::region`): only the deeply-shared classes (Immutable, Cown)
/// qualify. This is the membership/borrow predicate, NOT the reference-count
/// atomicity one -- see [`rc_atomic`].
#[inline]
pub fn is_shared(owner: u8) -> bool {
    owner >= OWNER_IMMUTABLE
}

/// Whether an object's reference count must be maintained atomically. A `Bridge`
/// is a region's external entry point reachable from another thread (the
/// `with`-acquired cown a `spawn` capture is promoted to), so its count is touched
/// concurrently even though region *membership* (`is_shared`) excludes it. The
/// `Bridge`/`Immutable`/`Cown` classes are the ones that cross threads; `Local`
/// and `Contained` (region-interior, reached only under the bridge's lock) stay on
/// the fast non-atomic path. A capture is promoted to one of these atomic classes
/// *before* the spawn (freeze/cown), so its owner -- and thus its atomicity -- is
/// stable from the first cross-thread reference.
#[inline]
pub fn rc_atomic(owner: u8) -> bool {
    owner >= OWNER_BRIDGE
}

/// Heap object header. `owner` classifies reference-count behavior (see the owner
/// constants); `rc` is the reference count the typed back end maintains (DESIGN.md
/// 8.2). `color`/`flags`/`nchild` are reserved for region metadata.
#[repr(C)]
pub struct Header {
    pub rc: i64,
    pub owner: u8,
    pub kind: u8,
    pub color: u8,
    pub flags: u8,
    pub nchild: i32,
}

// The bump allocator lives in crate::mem.
pub use crate::mem::pp_obj_alloc;

/// Mask an integer to the width/signedness implied by its tag. Used by the typed
/// conversion entry points to store a converted value at its target width.
pub fn mask_int(v: i64, tag: i64) -> i64 {
    let (bits, signed) = match tag {
        TAG_INT_I8 => (8, true),
        TAG_INT_I16 => (16, true),
        TAG_INT_I32 => (32, true),
        TAG_INT_U8 => (8, false),
        TAG_INT_U16 => (16, false),
        TAG_INT_U32 => (32, false),
        _ => return v, // 64-bit kinds: no masking
    };
    let m: i128 = (1i128 << bits) - 1;
    let raw = (v as i128) & m;
    if signed {
        let sign = 1i128 << (bits - 1);
        let val = if raw & sign != 0 {
            raw - (1i128 << bits)
        } else {
            raw
        };
        val as i64
    } else {
        raw as i64
    }
}
