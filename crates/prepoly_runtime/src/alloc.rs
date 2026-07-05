//! Heap allocation of the typed back end's objects. Everything
//! is bump-allocated through `crate::mem`; objects are never individually freed.
//! These are the typed string, array, and conversion-helper entry points the
//! unboxed code generator calls: their values are concrete unboxed typed data.

use std::os::raw::c_void;
use std::sync::atomic::{AtomicI64, Ordering};

use crate::rt::*;

/// Initialize the 16-byte object header. `nchild` is recorded for layout
/// compatibility only; nothing reclaims based on it.
unsafe fn init_header(p: *mut c_void, kind: u8, nchild: i32) -> *mut Header {
    unsafe {
        let h = p as *mut Header;
        (*h).rc = 1;
        (*h).owner = OWNER_LOCAL;
        (*h).kind = kind;
        (*h).color = 0;
        (*h).flags = 0;
        (*h).nchild = nchild;
        h
    }
}

/// View an object's reference count as atomic, for frozen objects shared across
/// threads (`rc` is `i64`, so this is layout-identical).
unsafe fn atomic_rc<'a>(h: *mut Header) -> &'a AtomicI64 {
    unsafe { &*(std::ptr::addr_of!((*h).rc) as *const AtomicI64) }
}

/// Increment `h`'s reference count: a new reference is being created -- a binding,
/// field store, capture, or argument. A shared object's count
/// (Immutable/Cown) is atomic because it may be reached from several threads; an
/// owned object's (Local/Contained/Bridge) is not.
///
/// # Safety
/// `h` must be a valid object header (or null).
pub unsafe extern "C-unwind" fn pp_retain(h: *mut Header) {
    unsafe {
        if h.is_null() {
            return;
        }
        if rc_atomic((*h).owner) {
            atomic_rc(h).fetch_add(1, Ordering::Relaxed);
        } else {
            (*h).rc += 1;
        }
    }
}

/// Decrement `h`'s reference count and free the object when it reaches zero. Frees
/// only this object: releasing the objects it references is the typed back end's
/// recursive-destructor responsibility (it owns the field layout). The frozen
/// path uses release/acquire so the freeing thread observes all prior writes.
///
/// # Safety
/// `h` must be a valid object header (or null).
pub unsafe extern "C-unwind" fn pp_release(h: *mut Header) {
    unsafe {
        if h.is_null() {
            return;
        }
        let dead = if rc_atomic((*h).owner) {
            let was = atomic_rc(h).fetch_sub(1, Ordering::Release);
            if was == 1 {
                std::sync::atomic::fence(Ordering::Acquire);
                true
            } else {
                false
            }
        } else {
            (*h).rc -= 1;
            (*h).rc <= 0
        };
        if dead {
            crate::mem::pp_obj_free(h as *mut c_void);
        }
    }
}

/// Mark `h` deeply immutable and shareable across threads (the `freeze`
/// operation): its reference count becomes atomic. This sets the marker on `h`;
/// freezing the objects it transitively references is the back end's traversal.
///
/// # Safety
/// `h` must be a valid object header (or null).
pub unsafe extern "C-unwind" fn pp_freeze(h: *mut Header) {
    unsafe {
        if !h.is_null() {
            (*h).owner = OWNER_FROZEN;
        }
    }
}

/// Allocate a typed monomorphized heap object of `size` bytes (header + the
/// back end's own typed field layout) and return its header pointer. The object
/// has `KIND_TYPED`: the typed back end lays out and accesses the fields itself. Used by the unboxed codegen path.
pub extern "C-unwind" fn pp_typed_alloc(size: i64) -> *mut Header {
    unsafe { init_header(pp_obj_alloc(size), KIND_TYPED, 0) }
}

// ----- growable typed array (unboxed backend) -----
//
// Layout: { header(16) | len: i64 @16 | cap: i64 @24 | data: *u8 @32 }, with a
// separately-allocated element buffer of `cap * elem_size` bytes. Elements are
// concrete typed values, not boxed `Value`.

/// `count * elem_size` as a byte length, trapping on a negative operand or i64
/// overflow. Generated code supplies these, so a bad length must fail closed
/// rather than wrap into an undersized allocation that later element writes
/// overrun. `pp_panic_str` exits the process (no unwind across the C-ABI).
fn checked_bytes(count: i64, elem_size: i64) -> i64 {
    if count < 0 || elem_size < 0 {
        crate::builtins::pp_panic_str("negative array allocation size");
    }
    match count.checked_mul(elem_size) {
        Some(n) => n,
        None => crate::builtins::pp_panic_str("array allocation size overflow"),
    }
}

/// Double a capacity for growth, trapping on overflow (never below 4).
fn grow_cap(cap: i64) -> i64 {
    match cap.checked_mul(2) {
        Some(c) => c.max(4),
        None => crate::builtins::pp_panic_str("array capacity overflow"),
    }
}

/// A growable array holding `len` elements with spare capacity.
pub extern "C-unwind" fn pp_arr_new(elem_size: i64, len: i64) -> *mut Header {
    unsafe {
        let cap = len.max(4);
        let h = pp_typed_alloc(40);
        *((h as *mut u8).offset(16) as *mut i64) = len;
        *((h as *mut u8).offset(24) as *mut i64) = cap;
        let data = pp_obj_alloc(checked_bytes(cap, elem_size.max(1))) as *mut u8;
        *((h as *mut u8).offset(32) as *mut *mut u8) = data;
        h
    }
}

/// A fresh growable array with the same elements as `arr` (the value-passing of a
/// non-reference array argument). The element bytes are copied into a new buffer;
/// when `managed != 0` the elements are heap pointers shared with the original, so
/// each is retained (a one-level copy with sound reference counts).
///
/// # Safety
/// `arr` must be a growable-array object whose elements are `elem_size` bytes each.
pub unsafe extern "C-unwind" fn pp_arr_copy(
    arr: *mut Header,
    elem_size: i64,
    managed: i64,
) -> *mut Header {
    unsafe {
        let len = *((arr as *mut u8).offset(16) as *mut i64);
        let src = *((arr as *mut u8).offset(32) as *mut *mut u8);
        let new = pp_arr_new(elem_size, len);
        let dst = *((new as *mut u8).offset(32) as *mut *mut u8);
        std::ptr::copy_nonoverlapping(src, dst, (len * elem_size) as usize);
        if managed != 0 {
            for i in 0..len {
                let slot = dst.offset((i * elem_size) as isize) as *mut *mut Header;
                if !(*slot).is_null() {
                    pp_retain(*slot);
                }
            }
        }
        new
    }
}

/// A fresh growable array deep-copying each element of `arr`. When `copy_fn` is 0
/// the elements are plain bytes and the buffer is copied directly; otherwise each
/// element is a heap pointer and `copy_fn` (a `fn(*Header) -> *Header`) produces an
/// independent copy of it, recursing for nested aggregates.
///
/// # Safety
/// `arr` must be a growable-array object whose elements are `elem_size` bytes each;
/// when `copy_fn != 0` it must be a valid `extern "C-unwind" fn(*mut Header) ->
/// *mut Header` and the elements must be `*mut Header` pointers.
pub unsafe extern "C-unwind" fn pp_arr_deep_copy(
    arr: *mut Header,
    elem_size: i64,
    copy_fn: usize,
) -> *mut Header {
    unsafe {
        let len = *((arr as *mut u8).offset(16) as *mut i64);
        let src = *((arr as *mut u8).offset(32) as *mut *mut u8);
        let new = pp_arr_new(elem_size, len);
        let dst = *((new as *mut u8).offset(32) as *mut *mut u8);
        if copy_fn == 0 {
            std::ptr::copy_nonoverlapping(src, dst, (len * elem_size) as usize);
        } else {
            let f: extern "C-unwind" fn(*mut Header) -> *mut Header = std::mem::transmute(copy_fn);
            for i in 0..len {
                let elem = *(src.offset((i * elem_size) as isize) as *mut *mut Header);
                let copied = if elem.is_null() { elem } else { f(elem) };
                *(dst.offset((i * elem_size) as isize) as *mut *mut Header) = copied;
            }
        }
        new
    }
}

/// Append `elem_size` bytes from `elem` to the array, growing (doubling) the
/// element buffer if full.
///
/// # Safety
/// `arr` must be a growable-array object and `elem` must point to at least
/// `elem_size` readable bytes.
pub unsafe extern "C-unwind" fn pp_arr_push(arr: *mut Header, elem: *const u8, elem_size: i64) {
    unsafe {
        let len_p = (arr as *mut u8).offset(16) as *mut i64;
        let cap_p = (arr as *mut u8).offset(24) as *mut i64;
        let data_pp = (arr as *mut u8).offset(32) as *mut *mut u8;
        let (len, cap) = (*len_p, *cap_p);
        if len == cap {
            let new_cap = grow_cap(cap);
            let new_data = pp_obj_alloc(checked_bytes(new_cap, elem_size)) as *mut u8;
            let old = *data_pp;
            std::ptr::copy_nonoverlapping(old, new_data, (len * elem_size) as usize);
            *data_pp = new_data;
            *cap_p = new_cap;
            // The old element buffer is now unreferenced (its contents were copied;
            // for heap elements only the pointers moved, so the elements stay live
            // in the new buffer). Reclaim it -- a sound, owned-by-the-array free.
            crate::mem::pp_obj_free(old as *mut c_void);
        }
        let dst = (*data_pp).offset((len * elem_size) as isize);
        std::ptr::copy_nonoverlapping(elem, dst, elem_size as usize);
        *len_p = len + 1;
    }
}

/// Insert `elem_size` bytes from `elem` at index `idx` (`_array_insert`), shifting the elements at and after `idx` one slot toward the end and
/// growing the buffer if full. `idx` is clamped to `[0, len]` (an `idx == len`
/// insert is an append).
///
/// # Safety
/// `arr` must be a growable-array object and `elem` must point to at least
/// `elem_size` readable bytes.
pub unsafe extern "C-unwind" fn pp_arr_insert(
    arr: *mut Header,
    idx: i64,
    elem: *const u8,
    elem_size: i64,
) {
    unsafe {
        let len_p = (arr as *mut u8).offset(16) as *mut i64;
        let cap_p = (arr as *mut u8).offset(24) as *mut i64;
        let data_pp = (arr as *mut u8).offset(32) as *mut *mut u8;
        let (len, cap) = (*len_p, *cap_p);
        if len == cap {
            let new_cap = grow_cap(cap);
            let new_data = pp_obj_alloc(checked_bytes(new_cap, elem_size)) as *mut u8;
            let old = *data_pp;
            std::ptr::copy_nonoverlapping(old, new_data, (len * elem_size) as usize);
            *data_pp = new_data;
            *cap_p = new_cap;
            crate::mem::pp_obj_free(old as *mut c_void);
        }
        let at = idx.clamp(0, len);
        let base = *data_pp;
        // Shift [at, len) right by one element to open a hole at `at`.
        let src = base.offset((at * elem_size) as isize);
        let dst = base.offset(((at + 1) * elem_size) as isize);
        std::ptr::copy(src, dst, ((len - at) * elem_size) as usize);
        std::ptr::copy_nonoverlapping(elem, src, elem_size as usize);
        *len_p = len + 1;
    }
}

/// Remove and return the element at index `idx` (`_array_remove`),
/// shifting the elements after it one slot toward the front. The removed element's
/// bytes are returned zero-extended in an `i64` (every typed slice element -- a
/// scalar or a heap pointer -- is at most 8 bytes); the caller reinterprets them at
/// the element type. An out-of-range `idx` returns 0 without modifying the array.
///
/// # Safety
/// `arr` must be a growable-array object whose elements are `elem_size` bytes each.
pub unsafe extern "C-unwind" fn pp_arr_remove(arr: *mut Header, idx: i64, elem_size: i64) -> i64 {
    unsafe {
        let len_p = (arr as *mut u8).offset(16) as *mut i64;
        let data_pp = (arr as *mut u8).offset(32) as *mut *mut u8;
        let len = *len_p;
        if idx < 0 || idx >= len {
            return 0;
        }
        let base = *data_pp;
        let slot = base.offset((idx * elem_size) as isize);
        // Read the removed element's bytes into the low bits of an i64.
        let mut bits: i64 = 0;
        std::ptr::copy_nonoverlapping(
            slot,
            &mut bits as *mut i64 as *mut u8,
            elem_size.min(8) as usize,
        );
        // Shift (idx, len) left by one element to close the gap.
        let next = base.offset(((idx + 1) * elem_size) as isize);
        std::ptr::copy(next, slot, ((len - idx - 1) * elem_size) as usize);
        *len_p = len - 1;
        bits
    }
}

/// Remove and return the last element as a nullable (`_array_pop`):
/// a heap cell `{ header16 | value@16 }` holding the element's bytes, or a null
/// pointer when the array is empty. The element's ownership transfers to the cell
/// (the array's length shrinks), mirroring `pp_str_char_at`'s nullable result, so
/// no extra retain/release is needed for a managed element.
///
/// # Safety
/// `arr` must be a growable-array object whose elements are `elem_size` bytes each.
pub unsafe extern "C-unwind" fn pp_arr_pop(arr: *mut Header, elem_size: i64) -> *mut Header {
    unsafe {
        let len_p = (arr as *mut u8).offset(16) as *mut i64;
        let data_pp = (arr as *mut u8).offset(32) as *mut *mut u8;
        let len = *len_p;
        if len <= 0 {
            return std::ptr::null_mut();
        }
        let slot = (*data_pp).offset(((len - 1) * elem_size) as isize);
        let cell = pp_typed_alloc(24);
        // Copy the element bytes into the cell's value slot (zero the slot first so
        // a sub-8-byte scalar leaves no stale high bits).
        let value_p = (cell as *mut u8).offset(16);
        std::ptr::write_bytes(value_p, 0, 8);
        std::ptr::copy_nonoverlapping(slot, value_p, elem_size.min(8) as usize);
        *len_p = len - 1;
        cell
    }
}

// ----- typed string entry points (unboxed backend) -----
//
// A typed string is the header pointer of a `KIND_STRING` object with layout
// `{ header(16) | len: i64 @16 | bytes[len] @24 }`. These let the typed code
// generator build and use strings without boxing.

unsafe fn str_bytes_ptr(h: *mut Header) -> *const u8 {
    unsafe { (h as *const u8).offset(24) }
}

/// A `&str` view of a typed `KIND_STRING` object (for runtime conversions).
pub(crate) unsafe fn typed_str(h: *mut Header) -> &'static str {
    unsafe {
        let len = pp_str_len(h) as usize;
        std::str::from_utf8_unchecked(std::slice::from_raw_parts(str_bytes_ptr(h), len))
    }
}

/// Build a typed `Result` object `{ header16 | i32 tag@16 | payload@24 }` (the
/// layout the typed back end reads). `ok` selects the Ok/Err tag (0/1); the
/// payload (up to 8 bytes) is written by `write`.
pub(crate) unsafe fn typed_result(ok: bool, write: impl FnOnce(*mut u8)) -> *mut Header {
    unsafe {
        let h = pp_typed_alloc(32);
        *((h as *mut u8).offset(16) as *mut i32) = if ok { 0 } else { 1 };
        write((h as *mut u8).offset(24));
        h
    }
}

/// A typed `Result.Err { error: <msg> }`.
pub(crate) unsafe fn typed_result_err(msg: &str) -> *mut Header {
    unsafe {
        let s = pp_str_const(msg.as_ptr(), msg.len() as i64);
        typed_result(false, |p| *(p as *mut *mut Header) = s)
    }
}

/// A string object from raw UTF-8 bytes (a string literal).
///
/// # Safety
/// `ptr` must point to at least `len` readable bytes.
pub unsafe extern "C-unwind" fn pp_str_const(ptr: *const u8, len: i64) -> *mut Header {
    unsafe {
        if len < 0 {
            crate::builtins::pp_panic_str("negative string length");
        }
        let h = init_header(pp_obj_alloc(len.saturating_add(24)), KIND_STRING, 0);
        *((h as *mut u8).offset(16) as *mut i64) = len;
        std::ptr::copy_nonoverlapping(ptr, str_bytes_ptr(h) as *mut u8, len as usize);
        h
    }
}

/// The byte length of a string object.
///
/// # Safety
/// `h` must be a string object.
pub unsafe extern "C-unwind" fn pp_str_len(h: *mut Header) -> i64 {
    unsafe { *((h as *const u8).offset(16) as *const i64) }
}

/// A fresh string object that is the concatenation of two strings.
///
/// # Safety
/// `a` and `b` must be string objects.
pub unsafe extern "C-unwind" fn pp_str_concat(a: *mut Header, b: *mut Header) -> *mut Header {
    unsafe {
        let (la, lb) = (pp_str_len(a) as usize, pp_str_len(b) as usize);
        let mut buf = Vec::with_capacity(la + lb);
        buf.extend_from_slice(std::slice::from_raw_parts(str_bytes_ptr(a), la));
        buf.extend_from_slice(std::slice::from_raw_parts(str_bytes_ptr(b), lb));
        pp_str_const(buf.as_ptr(), buf.len() as i64)
    }
}

/// Whether two strings have equal bytes. Null-safe: a null operand (an absent
/// `string?` the checker let flow into `==`) equals only another null, matching
/// the interpreter's identity rule instead of faulting on the dereference.
///
/// # Safety
/// `a` and `b` must be string objects or null.
pub unsafe extern "C-unwind" fn pp_str_eq(a: *mut Header, b: *mut Header) -> bool {
    if a.is_null() || b.is_null() {
        return a.is_null() && b.is_null();
    }
    unsafe {
        let (la, lb) = (pp_str_len(a) as usize, pp_str_len(b) as usize);
        la == lb
            && std::slice::from_raw_parts(str_bytes_ptr(a), la)
                == std::slice::from_raw_parts(str_bytes_ptr(b), lb)
    }
}

/// Lexicographic (byte-order) comparison of two strings (`_string_cmp`): -1 if `a < b`, 0 if equal, 1 if `a > b`.
///
/// # Safety
/// `a` and `b` must be string objects.
pub unsafe extern "C-unwind" fn pp_str_cmp(a: *mut Header, b: *mut Header) -> i32 {
    unsafe {
        let (la, lb) = (pp_str_len(a) as usize, pp_str_len(b) as usize);
        let ba = std::slice::from_raw_parts(str_bytes_ptr(a), la);
        let bb = std::slice::from_raw_parts(str_bytes_ptr(b), lb);
        match ba.cmp(bb) {
            std::cmp::Ordering::Less => -1,
            std::cmp::Ordering::Equal => 0,
            std::cmp::Ordering::Greater => 1,
        }
    }
}

/// Substring `[start, end)` of a string (typed). The range is clamped to the
/// string's bounds and each endpoint snapped back to the nearest UTF-8 character
/// boundary, matching the interpreter's `string_slice`: a mid-character byte
/// range must not materialize invalid UTF-8 (later string primitives assume
/// validity via `from_utf8_unchecked`).
///
/// # Safety
/// `s` must be a string object.
pub unsafe extern "C-unwind" fn pp_str_slice(s: *mut Header, start: i64, end: i64) -> *mut Header {
    unsafe {
        let len = pp_str_len(s);
        let st = start.clamp(0, len) as usize;
        // Clamp the end against the already-clamped start, not the raw `start`:
        // a `start > len` would make the range `clamp(min > max)` and panic
        // (aborting the process across the C-ABI boundary) instead of yielding
        // an empty slice.
        let en = end.clamp(st as i64, len) as usize;
        let bytes = std::slice::from_raw_parts(str_bytes_ptr(s), len as usize);
        let st = snap_char_boundary(bytes, st);
        let en = snap_char_boundary(bytes, en);
        pp_str_const(bytes[st..en].as_ptr(), (en - st) as i64)
    }
}

/// Move `i` back to the nearest UTF-8 character boundary at or before it
/// (continuation bytes have the form `0b10xx_xxxx`).
fn snap_char_boundary(bytes: &[u8], mut i: usize) -> usize {
    while i > 0 && i < bytes.len() && (bytes[i] & 0xC0) == 0x80 {
        i -= 1;
    }
    i
}

/// The byte index of `sub` in `s`, or null (typed `_string_find`): a nullable
/// `int64` -- a heap cell `{ header16 | i64@16 }` when found, else a null pointer.
///
/// # Safety
/// `s` and `sub` must be string objects.
pub unsafe extern "C-unwind" fn pp_str_find(s: *mut Header, sub: *mut Header) -> *mut Header {
    unsafe {
        match typed_str(s).find(typed_str(sub)) {
            Some(pos) => {
                let cell = pp_typed_alloc(24);
                *((cell as *mut u8).offset(16) as *mut i64) = pos as i64;
                cell
            }
            None => std::ptr::null_mut(),
        }
    }
}

/// The bytes of a string as a growable `uint8[]` (typed). The elements are
/// unboxed `u8`.
///
/// # Safety
/// `s` must be a string object.
pub unsafe extern "C-unwind" fn pp_str_to_bytes(s: *mut Header) -> *mut Header {
    unsafe {
        let len = pp_str_len(s);
        let arr = pp_arr_new(1, len);
        let dst = *((arr as *mut u8).offset(32) as *mut *mut u8);
        std::ptr::copy_nonoverlapping(str_bytes_ptr(s), dst, len as usize);
        arr
    }
}

/// A copy of `s` with four spaces inserted after each newline, indenting every
/// line after the first by one level. The typed `to_string` of records and sums
/// uses this to nest a field's multi-line rendering one level deeper under its
/// label, so arbitrarily nested values pretty-print with increasing indentation.
///
/// # Safety
/// `s` must be a string object.
pub unsafe extern "C-unwind" fn pp_str_indent(s: *mut Header) -> *mut Header {
    unsafe {
        let indented = typed_str(s).replace('\n', "\n    ");
        pp_str_const(indented.as_ptr(), indented.len() as i64)
    }
}

/// Render an integer as a string (`signed != 0` selects signed decimal). For
/// typed string interpolation.
pub extern "C-unwind" fn pp_int_to_str(v: i64, signed: i64) -> *mut Header {
    let s = if signed != 0 {
        v.to_string()
    } else {
        (v as u64).to_string()
    };
    // The pointer/length come from a live local `String`, so they are valid.
    unsafe { pp_str_const(s.as_ptr(), s.len() as i64) }
}

/// Render a float as a string: an integral finite value below 1e15 keeps a
/// trailing `.0`.
pub extern "C-unwind" fn pp_float_to_str(v: f64) -> *mut Header {
    let s = if v.is_finite() && v == v.trunc() && v.abs() < 1e15 {
        format!("{v:.1}")
    } else {
        format!("{v}")
    };
    // The pointer/length come from a live local `String`, so they are valid.
    unsafe { pp_str_const(s.as_ptr(), s.len() as i64) }
}

/// Write a string's bytes to stdout (typed `print`).
///
/// # Safety
/// `h` must be a string object.
pub unsafe extern "C-unwind" fn pp_print_str(h: *mut Header) {
    use std::io::Write;
    unsafe {
        let len = pp_str_len(h) as usize;
        let bytes = std::slice::from_raw_parts(str_bytes_ptr(h), len);
        let _ = std::io::stdout().write_all(bytes);
    }
}

/// Write a string's bytes to stdout followed by a newline (typed `println`).
///
/// # Safety
/// `h` must be a string object.
pub unsafe extern "C-unwind" fn pp_println_str(h: *mut Header) {
    use std::io::Write;
    unsafe {
        let len = pp_str_len(h) as usize;
        let bytes = std::slice::from_raw_parts(str_bytes_ptr(h), len);
        let mut out = std::io::stdout();
        let _ = out.write_all(bytes);
        let _ = out.write_all(b"\n");
    }
}

/// Render a bool as `"true"`/`"false"`.
pub extern "C-unwind" fn pp_bool_to_str(v: i64) -> *mut Header {
    let s = if v != 0 { "true" } else { "false" };
    // The pointer/length come from a static string literal, so they are valid.
    unsafe { pp_str_const(s.as_ptr(), s.len() as i64) }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Serialize against every other test that touches the shared heap. These
    /// tests allocate and free through the process-global allocator (mutating the
    /// `LIVE_BLOCKS` counter and ticking the GC schedule), so without this guard
    /// they run concurrently with the gc/conc tests whose exact live-block
    /// assertions the stray allocations would perturb (see `serial_heap_test`).
    fn serial() -> std::sync::MutexGuard<'static, ()> {
        crate::serial_heap_test()
    }

    /// Allocation starts at rc 1; retain/release move it and the object is freed
    /// when the count reaches zero (the local, non-atomic path).
    #[test]
    fn refcount_retain_release_and_free() {
        let _serial = serial();
        unsafe {
            let h = pp_typed_alloc(32);
            assert_eq!((*h).rc, 1, "fresh object owns one reference");
            assert_eq!((*h).owner, OWNER_LOCAL);
            pp_retain(h);
            assert_eq!((*h).rc, 2);
            pp_release(h);
            assert_eq!((*h).rc, 1, "still alive after one release");
            // The last release drops to zero and frees; nothing reads `h` after.
            pp_release(h);
        }
    }

    /// A frozen object uses an atomic reference count (it may be shared across
    /// threads), and `pp_freeze` records the owner class.
    #[test]
    fn frozen_uses_atomic_refcount() {
        let _serial = serial();
        unsafe {
            let h = pp_typed_alloc(16);
            pp_freeze(h);
            assert_eq!((*h).owner, OWNER_FROZEN);
            pp_retain(h);
            assert_eq!((*h).rc, 2);
            pp_release(h);
            assert_eq!((*h).rc, 1);
            pp_release(h);
        }
    }

    /// Null is a no-op for every reference-counting primitive (a nullable slot may
    /// hold null).
    #[test]
    fn refcount_ops_tolerate_null() {
        let _serial = serial();
        unsafe {
            pp_retain(std::ptr::null_mut());
            pp_release(std::ptr::null_mut());
            pp_freeze(std::ptr::null_mut());
        }
    }

    /// `pp_arr_insert` opens a hole at the index (shifting the tail right) and
    /// `pp_arr_remove` returns the element and closes the gap (shifting left).
    #[test]
    fn array_insert_and_remove_shift_elements() {
        let _serial = serial();
        unsafe {
            let arr = pp_arr_new(8, 0);
            for v in [10i64, 20, 30] {
                pp_arr_push(arr, &v as *const i64 as *const u8, 8);
            }
            // [10, 20, 30] -> insert 15 at index 1 -> [10, 15, 20, 30]
            let x: i64 = 15;
            pp_arr_insert(arr, 1, &x as *const i64 as *const u8, 8);
            let len = *((arr as *mut u8).offset(16) as *mut i64);
            let data = *((arr as *mut u8).offset(32) as *mut *mut u8);
            assert_eq!(len, 4);
            let view: Vec<i64> = (0..4).map(|i| *(data as *const i64).offset(i)).collect();
            assert_eq!(view, vec![10, 15, 20, 30]);

            // remove index 0 -> returns 10, leaves [15, 20, 30]
            let removed = pp_arr_remove(arr, 0, 8);
            assert_eq!(removed, 10);
            let len = *((arr as *mut u8).offset(16) as *mut i64);
            let view: Vec<i64> = (0..len)
                .map(|i| *(data as *const i64).offset(i as isize))
                .collect();
            assert_eq!(view, vec![15, 20, 30]);

            // out-of-range remove is a no-op returning 0
            assert_eq!(pp_arr_remove(arr, 99, 8), 0);
            assert_eq!(*((arr as *mut u8).offset(16) as *mut i64), 3);
        }
    }

    /// `pp_arr_pop` returns the last element in a nullable cell and shrinks the
    /// array; popping an empty array yields a null pointer.
    #[test]
    fn array_pop_returns_last_or_null() {
        let _serial = serial();
        unsafe {
            let arr = pp_arr_new(8, 0);
            for v in [7i64, 8, 9] {
                pp_arr_push(arr, &v as *const i64 as *const u8, 8);
            }
            // pop -> 9, len 2
            let cell = pp_arr_pop(arr, 8);
            assert!(!cell.is_null());
            assert_eq!(*((cell as *mut u8).offset(16) as *mut i64), 9);
            assert_eq!(*((arr as *mut u8).offset(16) as *mut i64), 2);

            // drain the rest
            assert_eq!(*((pp_arr_pop(arr, 8) as *mut u8).offset(16) as *mut i64), 8);
            assert_eq!(*((pp_arr_pop(arr, 8) as *mut u8).offset(16) as *mut i64), 7);
            // empty -> null
            assert!(pp_arr_pop(arr, 8).is_null());
        }
    }

    /// Growing an array frees the old element buffer each time; the elements must
    /// survive the reallocation (only the buffer storage is reclaimed). If the
    /// free reclaimed live data, reading back would corrupt or fault.
    #[test]
    fn array_growth_frees_old_buffer_without_corrupting() {
        let _serial = serial();
        unsafe {
            let arr = pp_arr_new(8, 0);
            for i in 0..64i64 {
                pp_arr_push(arr, &i as *const i64 as *const u8, 8);
            }
            let len = *((arr as *mut u8).offset(16) as *mut i64);
            let data = *((arr as *mut u8).offset(32) as *mut *mut u8);
            assert_eq!(len, 64);
            for i in 0..64i64 {
                assert_eq!(*(data as *const i64).offset(i as isize), i);
            }
        }
    }

    /// `pp_str_cmp` orders strings lexicographically, returning -1 / 0 / 1.
    #[test]
    fn string_cmp_orders_lexicographically() {
        let _serial = serial();
        unsafe {
            let mk = |s: &str| pp_str_const(s.as_ptr(), s.len() as i64);
            assert_eq!(pp_str_cmp(mk("apple"), mk("banana")), -1);
            assert_eq!(pp_str_cmp(mk("banana"), mk("apple")), 1);
            assert_eq!(pp_str_cmp(mk("apple"), mk("apple")), 0);
            // A prefix sorts before the longer string.
            assert_eq!(pp_str_cmp(mk("app"), mk("apple")), -1);
        }
    }

    /// `pp_str_slice` clamps an out-of-range range to an empty slice instead of
    /// aborting. A `start` past the end used to make the end-clamp `min > max`
    /// and panic across the C-ABI boundary (a process abort mid-JIT-run).
    #[test]
    fn str_slice_out_of_range_yields_empty_not_abort() {
        let _serial = serial();
        unsafe {
            let s = pp_str_const("abc".as_ptr(), 3);
            // start beyond len: empty, no panic.
            let past = pp_str_slice(s, 10, 20);
            assert_eq!(pp_str_len(past), 0);
            // negative start, huge end: clamps to the whole string.
            let whole = pp_str_slice(s, -5, 100);
            assert_eq!(pp_str_len(whole), 3);
            // start > end after clamping: empty.
            let inverted = pp_str_slice(s, 2, 1);
            assert_eq!(pp_str_len(inverted), 0);
        }
    }
}
