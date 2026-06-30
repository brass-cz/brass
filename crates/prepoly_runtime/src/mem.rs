//! Runtime heap allocation. Each request is a zeroed allocation with a 16-byte
//! size prefix (so freeing needs no external metadata) and 16-byte alignment for
//! object headers. The size prefix lets [`pp_obj_free`] release a block by
//! reference count -- the substrate for region-based reclamation.

use std::alloc::{Layout, alloc_zeroed, dealloc};
use std::os::raw::c_void;
use std::sync::atomic::{AtomicI64, Ordering};

/// Count of blocks allocated but not yet freed. Used by tests to assert the
/// reference-counting back end balances allocation against reclamation (a leak
/// shows as a positive residue; a double free as a negative count). The
/// relaxed counter is cheap and only read in validation.
static LIVE_BLOCKS: AtomicI64 = AtomicI64::new(0);

/// The number of heap blocks currently live (allocated, not freed).
pub fn pp_live_blocks() -> i64 {
    LIVE_BLOCKS.load(Ordering::Relaxed)
}

/// The block layout for a body of `size` bytes: a 16-byte size prefix followed by
/// the object. Alloc and free must agree on it. Traps (rather than wrapping) on an
/// overflowing total so a bad length from generated code cannot produce an
/// undersized block; `pp_panic_str` exits the process, so it is safe to call
/// across the C-ABI boundary (no unwind into JIT frames).
fn block_layout(size: usize) -> Layout {
    let total = match size.checked_add(16) {
        Some(t) => t,
        None => crate::builtins::pp_panic_str("allocation size overflow"),
    };
    match Layout::from_size_align(total, 16) {
        Ok(l) => l,
        Err(_) => crate::builtins::pp_panic_str("invalid allocation layout"),
    }
}

unsafe fn raw_alloc(size: usize) -> *mut u8 {
    unsafe {
        let p = alloc_zeroed(block_layout(size));
        if p.is_null() {
            crate::builtins::pp_panic_str("out of memory");
        }
        *(p as *mut usize) = size;
        LIVE_BLOCKS.fetch_add(1, Ordering::Relaxed);
        p.add(16)
    }
}

/// Allocate a zeroed object of `size` bytes and return a pointer past the size
/// prefix. The header/body is laid out by the caller (the typed back end).
///
/// # Safety
/// `size` must be non-negative; the returned block must be freed with
/// [`pp_obj_free`].
pub unsafe fn pp_obj_alloc(size: i64) -> *mut c_void {
    // A negative size means an overflowing computed length wrapped; fail closed.
    if size < 0 {
        crate::builtins::pp_panic_str("negative allocation size");
    }
    unsafe { raw_alloc(size as usize) as *mut c_void }
}

/// Free a block allocated by [`pp_obj_alloc`], recovering the body size from the
/// 16-byte prefix. Frees only this block -- not separately-allocated element
/// buffers or referenced objects; a generated per-type destructor releases the
/// referenced objects first, then calls this. C-ABI so generated code can call it.
///
/// # Safety
/// `obj` must be a pointer returned by [`pp_obj_alloc`] that has not been freed
/// (or null).
pub unsafe extern "C-unwind" fn pp_obj_free(obj: *mut c_void) {
    unsafe {
        if obj.is_null() {
            return;
        }
        // Keep the cycle collector's registry free of dangling pointers.
        crate::gc::on_free(obj as *mut crate::rt::Header);
        let base = (obj as *mut u8).sub(16);
        let size = *(base as *mut usize);
        // Poison the freed body in debug builds so a use-after-free reads an obvious
        // sentinel (and a dangling pointer field faults) rather than stale-but-valid
        // data -- turning latent use-after-free into a visible failure during testing.
        #[cfg(debug_assertions)]
        std::ptr::write_bytes(obj as *mut u8, 0xDE, size);
        LIVE_BLOCKS.fetch_sub(1, Ordering::Relaxed);
        dealloc(base, block_layout(size));
    }
}
