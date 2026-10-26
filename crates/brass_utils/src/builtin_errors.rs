//! Shared failure texts for runtime operations and builtin `Err` payloads.
//!
//! The payload is an ordinary program value -- it can be printed, compared, or
//! matched on -- so the compiled runtime (`brass_runtime`) and the REPL
//! interpreter must produce exactly the same text. Both build their messages
//! here.

use crate::float_str;

/// A load or store uses an array index outside its current length.
pub const ARRAY_INDEX_OUT_OF_BOUNDS: &str = "array index out of bounds";

/// The `Err` payload of `_string_from_bytes` (and the prelude's `to_text`) for
/// a byte sequence that is not valid UTF-8.
pub const INVALID_UTF8: &str = "invalid UTF-8 byte sequence";

/// An integer conversion's source `value` lies outside the target type
/// `type_name`'s range `min..=max`.
pub fn int_out_of_range(value: i128, type_name: &str, min: i128, max: i128) -> String {
    format!("integer value {value} is out of range for {type_name} ({min}..={max})")
}

/// A float-to-integer conversion's source `value` (finite, truncated toward
/// zero) lies outside the target type `type_name`'s range `min..=max`.
pub fn float_out_of_range(value: f64, type_name: &str, min: i128, max: i128) -> String {
    format!(
        "float value {} is out of range for {type_name} ({min}..={max})",
        float_str(value)
    )
}

/// A float-to-integer conversion of a NaN or infinite `value`.
pub fn non_finite_to_int(value: f64, type_name: &str) -> String {
    format!(
        "cannot convert non-finite float `{}` to {type_name}",
        float_str(value)
    )
}

/// `intN.parse(text)` / `floatN.parse(text)` on text that is not a number of
/// the requested `kind` (`"integer"` or `"float"`). `text` is quoted as given.
pub fn cannot_parse(text: &str, kind: &str) -> String {
    format!("cannot parse `{text}` as {kind}")
}
