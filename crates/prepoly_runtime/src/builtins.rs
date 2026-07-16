//! C-ABI runtime primitives the typed back end calls that are not pure string
//! construction (those live in `crate::alloc`): the typed numeric/string
//! conversions returning typed `Result`/nullable cells, and the panic path.

use crate::alloc::{pp_str_const, pp_typed_alloc, typed_result, typed_result_err, typed_str};
use crate::rt::*;

// ----- small helpers -----

unsafe fn cstr<'a>(p: *const u8, len: i64) -> &'a str {
    unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(p, len as usize)) }
}

/// Abort the process with a runtime error message. The typed back end has no
/// recoverable panic path, so this prints to stderr and exits. A message that
/// is already a rendered error trace (the prelude's unhandled-`!` rendering,
/// whose lines carry their own `[file:line:col] unhandled error:` framing)
/// prints verbatim; anything else keeps the `runtime error:` prefix.
pub fn pp_panic_str(msg: &str) -> ! {
    if msg.starts_with('[') && msg.contains("unhandled error:") {
        eprintln!("{msg}");
    } else {
        eprintln!("runtime error: {msg}");
    }
    std::process::exit(1);
}

/// Abort with a runtime error message (codegen-inserted panics).
///
/// # Safety
/// `p` must point to at least `len` readable UTF-8 bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn pp_panic(p: *const u8, len: i64) {
    pp_panic_str(unsafe { cstr(p, len) });
}

/// Abort with a typed-string message (the user-facing `_panic(msg)` builtin, where
/// `msg` is a runtime string value rather than a compile-time literal).
///
/// # Safety
/// `s` must be a string object.
pub unsafe extern "C-unwind" fn pp_panic_obj(s: *mut Header) {
    pp_panic_str(unsafe { typed_str(s) });
}

// ----- numeric ranges and formatting -----

fn int_range(tag: i64) -> Option<(i128, i128)> {
    Some(match tag {
        TAG_INT_I8 => (i8::MIN as i128, i8::MAX as i128),
        TAG_INT_I16 => (i16::MIN as i128, i16::MAX as i128),
        TAG_INT_I32 => (i32::MIN as i128, i32::MAX as i128),
        TAG_INT_I64 => (i64::MIN as i128, i64::MAX as i128),
        TAG_INT_U8 => (0, u8::MAX as i128),
        TAG_INT_U16 => (0, u16::MAX as i128),
        TAG_INT_U32 => (0, u32::MAX as i128),
        TAG_INT_U64 => (0, u64::MAX as i128),
        _ => return None,
    })
}

fn int_tag_name(t: i64) -> &'static str {
    match t {
        TAG_INT_I8 => "int8",
        TAG_INT_I16 => "int16",
        TAG_INT_I32 => "int32",
        TAG_INT_I64 => "int64",
        TAG_INT_U8 => "uint8",
        TAG_INT_U16 => "uint16",
        TAG_INT_U32 => "uint32",
        _ => "uint64",
    }
}

/// Render a float matching the typed string path: an integral finite value below
/// 1e15 keeps a trailing `.0`.
fn format_float(f: f64) -> String {
    if f.is_finite() && f == f.trunc() && f.abs() < 1e15 {
        format!("{f:.1}")
    } else {
        format!("{f}")
    }
}

/// Truncate a float toward zero to an integral value, range-checked against
/// `tag` and rejecting non-finite inputs.
fn float_to_integral(f: f64, tag: i64) -> Result<i128, String> {
    if !f.is_finite() {
        return Err(format!(
            "cannot convert non-finite float `{}` to {}",
            format_float(f),
            int_tag_name(tag)
        ));
    }
    let truncated = f.trunc();
    let (min, max) = int_range(tag).ok_or_else(|| format!("unknown integer tag `{tag}`"))?;
    if truncated < min as f64 || truncated > max as f64 {
        return Err(format!(
            "float value {} is out of range for {} ({}..={})",
            format_float(f),
            int_tag_name(tag),
            min,
            max
        ));
    }
    Ok(truncated as i128)
}

/// Range-check `n` against integer `tag`, returning the value masked to the
/// target width or the out-of-range message.
fn checked_int_i64(n: i128, tag: i64) -> Result<i64, String> {
    let (min, max) = int_range(tag).ok_or_else(|| format!("unknown integer tag `{tag}`"))?;
    if (min..=max).contains(&n) {
        Ok(mask_int(n as i64, tag))
    } else {
        Err(format!(
            "integer value {n} is out of range for {} ({}..={})",
            int_tag_name(tag),
            min,
            max
        ))
    }
}

/// Write an integer `val` at `p` at the width implied by `tag` (the typed
/// `Result`'s Ok payload uses the target type's native width).
unsafe fn write_int_at(p: *mut u8, val: i64, tag: i64) {
    unsafe {
        match tag {
            TAG_INT_I8 | TAG_INT_U8 => *(p as *mut i8) = val as i8,
            TAG_INT_I16 | TAG_INT_U16 => *(p as *mut i16) = val as i16,
            TAG_INT_I32 | TAG_INT_U32 => *(p as *mut i32) = val as i32,
            _ => *(p as *mut i64) = val,
        }
    }
}

// ----- typed conversions -----

/// Typed `Type.from(x)` for an integer target: convert an int (`is_float == 0`,
/// value in `xi`) or float (`xf`) to `tag` with a range check, returning a typed
/// `Result<intN, string>` (no boxed Value).
pub extern "C-unwind" fn pp_conv_int_from(
    xi: i64,
    is_float: i64,
    xf: f64,
    tag: i64,
) -> *mut Header {
    let n: Result<i128, String> = if is_float != 0 {
        float_to_integral(xf, tag)
    } else {
        Ok(xi as i128)
    };
    unsafe {
        match n.and_then(|n| checked_int_i64(n, tag)) {
            Ok(masked) => typed_result(true, |p| write_int_at(p, masked, tag)),
            Err(e) => typed_result_err(&e),
        }
    }
}

/// Typed `intN.parse(s)`: a typed `Result<intN, string>`.
///
/// # Safety
/// `s` must be a string object.
pub unsafe extern "C-unwind" fn pp_conv_int_parse(s: *mut Header, tag: i64) -> *mut Header {
    let text = unsafe { typed_str(s) };
    unsafe {
        match text.trim().parse::<i128>() {
            Ok(n) => match checked_int_i64(n, tag) {
                Ok(masked) => typed_result(true, |p| write_int_at(p, masked, tag)),
                Err(e) => typed_result_err(&e),
            },
            Err(_) => typed_result_err(&format!("cannot parse `{text}` as integer")),
        }
    }
}

/// The integer tag for a `(bit width, signedness)` pair, used by
/// the `_int_widen`/`_int_narrow` primitives whose width/sign arrive at runtime.
fn bits_to_int_tag(bits: i64, signed: bool) -> i64 {
    match (bits, signed) {
        (8, true) => TAG_INT_I8,
        (16, true) => TAG_INT_I16,
        (32, true) => TAG_INT_I32,
        (8, false) => TAG_INT_U8,
        (16, false) => TAG_INT_U16,
        (32, false) => TAG_INT_U32,
        (_, false) => TAG_INT_U64,
        (_, true) => TAG_INT_I64,
    }
}

/// `_int_widen(x, from_bits, to_bits, signed) -> int64`: widen the
/// `from_bits`-wide integer `x` to a wider type. Widening never loses information,
/// so this only re-establishes the value at full width (sign- or zero-extending the
/// source bits); `to_bits` is implied by the result type.
pub extern "C-unwind" fn pp_int_widen(x: i64, from_bits: i64, _to_bits: i64, signed: i64) -> i64 {
    mask_int(x, bits_to_int_tag(from_bits, signed != 0))
}

/// `_int_narrow(x, from_bits, to_bits, signed) -> int64!`: narrow
/// `x` to a `to_bits`-wide integer, returning a typed `Result` that is `Err` when
/// `x` is out of the target type's range.
pub extern "C-unwind" fn pp_int_narrow(
    x: i64,
    _from_bits: i64,
    to_bits: i64,
    signed: i64,
) -> *mut Header {
    let tag = bits_to_int_tag(to_bits, signed != 0);
    unsafe {
        match checked_int_i64(x as i128, tag) {
            Ok(masked) => typed_result(true, |p| write_int_at(p, masked, tag)),
            Err(e) => typed_result_err(&e),
        }
    }
}

/// Typed `floatN.from(x)` (infallible widening/narrowing): returns the float.
pub extern "C-unwind" fn pp_conv_float_from(xi: i64, is_float: i64, xf: f64, tag: i64) -> f64 {
    let f = if is_float != 0 { xf } else { xi as f64 };
    if tag == TAG_F32 { (f as f32) as f64 } else { f }
}

/// Typed `floatN.parse(s)`: a typed `Result<floatN, string>`.
///
/// # Safety
/// `s` must be a string object.
pub unsafe extern "C-unwind" fn pp_conv_float_parse(s: *mut Header, tag: i64) -> *mut Header {
    let text = unsafe { typed_str(s) };
    unsafe {
        match text.trim().parse::<f64>() {
            // The Ok payload type is `floatN`, so write it at that width: an f32
            // result must occupy the 4-byte slot the back end reads, not an f64
            // whose low half would be read as a garbage f32.
            Ok(f) if tag == TAG_F32 => typed_result(true, |p| *(p as *mut f32) = f as f32),
            Ok(f) => typed_result(true, |p| *(p as *mut f64) = f),
            Err(_) => typed_result_err(&format!("cannot parse `{text}` as float")),
        }
    }
}

// ----- typed string conversions -----

/// The UTF-8 character that begins at byte offset `i`. String indexing,
/// slicing, `find`, and `len` are all byte-offset based, so this
/// keeps `s[i]` consistent with them: it returns `None` when `i` is out of range
/// or lands in the middle of a multibyte character.
fn char_at_byte(s: &str, i: i64) -> Option<char> {
    if i < 0 {
        return None;
    }
    let i = i as usize;
    if i >= s.len() || !s.is_char_boundary(i) {
        return None;
    }
    s[i..].chars().next()
}

/// Typed `_string_char_at(s, i)`: the 1-character string at byte offset `i`, or
/// null -- a nullable string (heap cell `{ header16 | str ptr@16 }`, or null).
///
/// # Safety
/// `s` must be a string object.
pub unsafe extern "C-unwind" fn pp_str_char_at(s: *mut Header, i: i64) -> *mut Header {
    let text = unsafe { typed_str(s) };
    match char_at_byte(text, i) {
        Some(c) => unsafe {
            let cs = c.to_string();
            let sp = pp_str_const(cs.as_ptr(), cs.len() as i64);
            let cell = pp_typed_alloc(24);
            *((cell as *mut u8).offset(16) as *mut *mut Header) = sp;
            cell
        },
        None => std::ptr::null_mut(),
    }
}

/// Typed `_string_from_bytes(bytes)`: a typed `Result<string, string>` from a
/// `uint8[]` (growable array: len@16, data@32), validating UTF-8.
///
/// # Safety
/// `arr` must be a growable-array object of `u8` elements.
pub unsafe extern "C-unwind" fn pp_str_from_bytes(arr: *mut Header) -> *mut Header {
    unsafe {
        let len = *((arr as *mut u8).offset(16) as *mut i64) as usize;
        let data = *((arr as *mut u8).offset(32) as *mut *const u8);
        let bytes = std::slice::from_raw_parts(data, len).to_vec();
        match String::from_utf8(bytes) {
            Ok(s) => {
                let sp = pp_str_const(s.as_ptr(), s.len() as i64);
                typed_result(true, |p| *(p as *mut *mut Header) = sp)
            }
            Err(_) => typed_result_err("invalid UTF-8"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // String indexing is by UTF-8 byte offset; an offset inside a multi-byte
    // character, a negative offset, or one past the end yields no char.
    #[test]
    fn char_at_byte_uses_utf8_boundaries() {
        let s = "héllo"; // 'é' is two bytes at offsets 1..=2
        assert_eq!(char_at_byte(s, 0), Some('h'));
        assert_eq!(char_at_byte(s, 1), Some('é'));
        assert_eq!(char_at_byte(s, 2), None); // inside 'é'
        assert_eq!(char_at_byte(s, 3), Some('l'));
        assert_eq!(char_at_byte(s, -1), None);
        assert_eq!(char_at_byte(s, 100), None);
    }

    // Float-to-integer conversion truncates toward zero and rejects non-finite or
    // out-of-range inputs.
    #[test]
    fn float_to_integral_truncates_and_range_checks() {
        assert_eq!(float_to_integral(3.9, TAG_INT_I32), Ok(3));
        assert_eq!(float_to_integral(-3.9, TAG_INT_I32), Ok(-3));
        assert!(float_to_integral(1e20, TAG_INT_I32).is_err()); // out of range
        assert!(float_to_integral(f64::NAN, TAG_INT_I32).is_err());
        assert!(float_to_integral(f64::INFINITY, TAG_INT_I64).is_err());
    }

    // Range checking enforces each kind's bounds and masks to the target width.
    #[test]
    fn checked_int_enforces_range() {
        assert_eq!(checked_int_i64(200, TAG_INT_U8), Ok(200));
        assert!(checked_int_i64(256, TAG_INT_U8).is_err());
        assert!(checked_int_i64(-1, TAG_INT_U8).is_err());
        assert_eq!(checked_int_i64(127, TAG_INT_I8), Ok(127));
        assert!(checked_int_i64(128, TAG_INT_I8).is_err());
    }
}
