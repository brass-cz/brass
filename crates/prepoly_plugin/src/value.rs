//! Owned values and the Rust-type mapping used by plugin function adapters.

use core::ops::Deref;

use crate::raw::{self, RawValue};

/// The Prepoly-visible types a plugin function may take and return.
///
/// Four scalars and `string` are the leaves; `Bytes` is Prepoly's `uint8[]`,
/// which has its own type (rather than `Array(u8)`) because the boundary's
/// only integer is `int64` and byte buffers are encoded densely. Every other
/// sequence is `Array(T)`, recursively -- so `string[]`, `bool[]`, and
/// `string[][]` all exist without the boundary enumerating them.
///
/// The mapping to Prepoly source types is: `Void` -> no return, `Bool` ->
/// `bool`, `Int` -> `int64`, `Float` -> `float64`, `Str` -> `string`,
/// `Bytes` -> `uint8[]`, `Array(T)` -> `T[]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueType {
    Void,
    Bool,
    Int,
    Float,
    Str,
    Bytes,
    Array(Box<ValueType>),
}

impl ValueType {
    /// The array type with this element type.
    pub fn array_of(elem: ValueType) -> ValueType {
        ValueType::Array(Box::new(elem))
    }

    /// Append this type's signature encoding (see [`raw::RawFunction::sig`]).
    /// A leaf is one letter; an array is `a` followed by its element's
    /// encoding, so `as` is `string[]` and `aas` is `string[][]`. The `a`
    /// prefix keeps every encoding a valid identifier fragment, which the
    /// `_plugin_call_<code>` builtin names rely on.
    pub fn write_code(&self, out: &mut String) {
        match self {
            ValueType::Void => out.push('v'),
            ValueType::Bool => out.push('b'),
            ValueType::Int => out.push('i'),
            ValueType::Float => out.push('f'),
            ValueType::Str => out.push('s'),
            ValueType::Bytes => out.push('y'),
            ValueType::Array(elem) => {
                out.push('a');
                elem.write_code(out);
            }
        }
    }

    /// This type's signature encoding.
    pub fn code(&self) -> String {
        let mut s = String::new();
        self.write_code(&mut s);
        s
    }

    /// Decode one type from the front of `chars`, consuming exactly its
    /// encoding. `None` on an unknown letter or an `a` with no element.
    pub fn parse(chars: &mut core::str::Chars<'_>) -> Option<ValueType> {
        Some(match chars.next()? {
            'v' => ValueType::Void,
            'b' => ValueType::Bool,
            'i' => ValueType::Int,
            'f' => ValueType::Float,
            's' => ValueType::Str,
            'y' => ValueType::Bytes,
            'a' => ValueType::array_of(ValueType::parse(chars)?),
            _ => return None,
        })
    }

    /// Decode a type from a complete encoding (rejecting trailing text).
    pub fn from_code(code: &str) -> Option<ValueType> {
        let mut chars = code.chars();
        let ty = ValueType::parse(&mut chars)?;
        chars.next().is_none().then_some(ty)
    }

    /// The size, in bytes, of one element of this type inside a Prepoly array.
    /// A `bool` occupies one byte, every scalar eight, and every heap value
    /// (string, byte array, nested array) its pointer. Matches the typed back
    /// end's element layout.
    pub fn array_elem_size(&self) -> usize {
        match self {
            ValueType::Void => 0,
            ValueType::Bool => 1,
            _ => 8,
        }
    }
}

/// Prepoly's `uint8[]`: a byte buffer, encoded densely across the boundary.
///
/// A distinct type rather than `Vec<u8>` because `Vec<T>` is the general
/// array of `T`, and `u8` is not a boundary type of its own (the boundary's
/// integer is `int64`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Bytes(pub Vec<u8>);

impl Bytes {
    pub fn into_vec(self) -> Vec<u8> {
        self.0
    }
}

impl Deref for Bytes {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        &self.0
    }
}

impl From<Vec<u8>> for Bytes {
    fn from(v: Vec<u8>) -> Bytes {
        Bytes(v)
    }
}

/// An owned dynamically-typed value, the currency of plugin function
/// adapters on both sides of the boundary.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Void,
    Bool(bool),
    Int(i64),
    Float(f64),
    Str(String),
    Bytes(Vec<u8>),
    Array(Vec<Value>),
}

impl Value {
    /// Copy a host/plugin boundary value into an owned one.
    ///
    /// # Safety
    /// A buffer-carrying `raw` must point at a live buffer of `raw.len`
    /// elements ([`raw::TAG_STRING`] additionally UTF-8; [`raw::TAG_ARRAY`] a
    /// `RawValue` array, each element likewise live).
    pub unsafe fn from_raw(raw: &RawValue) -> Result<Value, String> {
        Ok(match raw.tag {
            raw::TAG_VOID => Value::Void,
            raw::TAG_BOOL => Value::Bool(raw.int != 0),
            raw::TAG_INT => Value::Int(raw.int),
            raw::TAG_FLOAT => Value::Float(raw.float),
            raw::TAG_STRING => {
                let bytes = unsafe { core::slice::from_raw_parts(raw.ptr, raw.len) };
                Value::Str(String::from_utf8_lossy(bytes).into_owned())
            }
            raw::TAG_BYTES => {
                let bytes = unsafe { core::slice::from_raw_parts(raw.ptr, raw.len) };
                Value::Bytes(bytes.to_vec())
            }
            raw::TAG_ARRAY => {
                let items = unsafe { raw_elems(raw) };
                Value::Array(
                    items
                        .iter()
                        .map(|e| unsafe { Value::from_raw(e) })
                        .collect::<Result<Vec<_>, _>>()?,
                )
            }
            other => return Err(format!("unknown value tag {other}")),
        })
    }

    /// Encode into a boundary value, leaking any buffer. The receiver owns
    /// the buffer and reclaims it with [`release_raw`] (host side: via the
    /// plugin's `prepoly_release` export).
    pub fn into_raw(self) -> RawValue {
        let mut out = RawValue::void();
        match self {
            Value::Void => {}
            Value::Bool(b) => {
                out.tag = raw::TAG_BOOL;
                out.int = i64::from(b);
            }
            Value::Int(i) => {
                out.tag = raw::TAG_INT;
                out.int = i;
            }
            Value::Float(f) => {
                out.tag = raw::TAG_FLOAT;
                out.float = f;
            }
            Value::Str(s) => {
                out.tag = raw::TAG_STRING;
                leak_into(s.into_bytes(), &mut out);
            }
            Value::Bytes(b) => {
                out.tag = raw::TAG_BYTES;
                leak_into(b, &mut out);
            }
            // Each element leaks its own buffer; `release_raw` walks the array
            // and reclaims them before the array itself.
            Value::Array(items) => {
                let elems: Box<[RawValue]> = items.into_iter().map(Value::into_raw).collect();
                out.tag = raw::TAG_ARRAY;
                out.len = elems.len();
                out.ptr = Box::into_raw(elems) as *const u8;
            }
        }
        out
    }
}

fn leak_into(bytes: Vec<u8>, out: &mut RawValue) {
    let boxed: Box<[u8]> = bytes.into_boxed_slice();
    out.len = boxed.len();
    out.ptr = Box::into_raw(boxed) as *const u8;
}

/// The elements of a [`raw::TAG_ARRAY`] value.
///
/// # Safety
/// `raw` must be a `TAG_ARRAY` value pointing at `raw.len` live `RawValue`s.
pub(crate) unsafe fn raw_elems<'a>(raw: &RawValue) -> &'a [RawValue] {
    if raw.len == 0 || raw.ptr.is_null() {
        return &[];
    }
    unsafe { core::slice::from_raw_parts(raw.ptr as *const RawValue, raw.len) }
}

/// Reclaim the buffer of a value produced by [`Value::into_raw`]. Only
/// meaningful inside the module that produced it (allocator identity).
///
/// # Safety
/// `raw` must come from `Value::into_raw` in this module and not have been
/// released before.
pub unsafe fn release_raw(raw: RawValue) {
    if raw.ptr.is_null() {
        return;
    }
    match raw.tag {
        raw::TAG_STRING | raw::TAG_BYTES => {
            let slice = core::ptr::slice_from_raw_parts_mut(raw.ptr as *mut u8, raw.len);
            drop(unsafe { Box::from_raw(slice) });
        }
        raw::TAG_ARRAY => {
            for e in unsafe { raw_elems(&raw) } {
                unsafe { release_raw(*e) };
            }
            let arr = core::ptr::slice_from_raw_parts_mut(raw.ptr as *mut RawValue, raw.len);
            drop(unsafe { Box::from_raw(arr) });
        }
        _ => {}
    }
}

/// A Rust type usable as a plugin function parameter.
pub trait FromValue: Sized {
    fn value_type() -> ValueType;
    fn from_value(v: Value) -> Result<Self, String>;
}

/// A Rust type usable as a plugin function result payload.
pub trait IntoValue {
    fn value_type() -> ValueType;
    fn into_value(self) -> Value;
}

fn mismatch(want: ValueType, got: &Value) -> String {
    format!("expected {want:?}, got {:?}", got.kind_name())
}

impl Value {
    /// A short name for diagnostics; a full [`ValueType`] is not recoverable
    /// from an empty array.
    fn kind_name(&self) -> &'static str {
        match self {
            Value::Void => "void",
            Value::Bool(_) => "bool",
            Value::Int(_) => "int",
            Value::Float(_) => "float",
            Value::Str(_) => "string",
            Value::Bytes(_) => "bytes",
            Value::Array(_) => "array",
        }
    }
}

macro_rules! scalar_conversions {
    ($($ty:ty => $vt:ident, $variant:ident;)+) => {
        $(
            impl FromValue for $ty {
                fn value_type() -> ValueType { ValueType::$vt }
                fn from_value(v: Value) -> Result<Self, String> {
                    match v {
                        Value::$variant(x) => Ok(x),
                        other => Err(mismatch(ValueType::$vt, &other)),
                    }
                }
            }
            impl IntoValue for $ty {
                fn value_type() -> ValueType { ValueType::$vt }
                fn into_value(self) -> Value { Value::$variant(self) }
            }
        )+
    };
}

scalar_conversions! {
    bool => Bool, Bool;
    i64 => Int, Int;
    f64 => Float, Float;
    String => Str, Str;
}

impl FromValue for Bytes {
    fn value_type() -> ValueType {
        ValueType::Bytes
    }
    fn from_value(v: Value) -> Result<Self, String> {
        match v {
            Value::Bytes(b) => Ok(Bytes(b)),
            other => Err(mismatch(ValueType::Bytes, &other)),
        }
    }
}

impl IntoValue for Bytes {
    fn value_type() -> ValueType {
        ValueType::Bytes
    }
    fn into_value(self) -> Value {
        Value::Bytes(self.0)
    }
}

/// `Vec<T>` is Prepoly's `T[]`, for any boundary element type -- including a
/// nested `Vec<Vec<String>>` (`string[][]`). Byte buffers are [`Bytes`], not
/// `Vec<u8>`.
impl<T: FromValue> FromValue for Vec<T> {
    fn value_type() -> ValueType {
        ValueType::array_of(T::value_type())
    }
    fn from_value(v: Value) -> Result<Self, String> {
        match v {
            Value::Array(items) => items.into_iter().map(T::from_value).collect(),
            other => Err(mismatch(ValueType::array_of(T::value_type()), &other)),
        }
    }
}

impl<T: IntoValue> IntoValue for Vec<T> {
    fn value_type() -> ValueType {
        ValueType::array_of(T::value_type())
    }
    fn into_value(self) -> Value {
        Value::Array(self.into_iter().map(T::into_value).collect())
    }
}

impl IntoValue for () {
    fn value_type() -> ValueType {
        ValueType::Void
    }
    fn into_value(self) -> Value {
        Value::Void
    }
}

/// A Rust return type of a plugin function: a plain [`IntoValue`] payload
/// (infallible), or `Result<payload, impl Display>` (fallible, surfacing in
/// Prepoly as `-> T!`).
pub trait IntoOutcome {
    const FALLIBLE: bool;
    fn value_type() -> ValueType;
    fn into_outcome(self) -> Result<Value, String>;
}

impl<T: IntoValue> IntoOutcome for T {
    const FALLIBLE: bool = false;
    fn value_type() -> ValueType {
        <T as IntoValue>::value_type()
    }
    fn into_outcome(self) -> Result<Value, String> {
        Ok(self.into_value())
    }
}

impl<T: IntoValue, E: core::fmt::Display> IntoOutcome for Result<T, E> {
    const FALLIBLE: bool = true;
    fn value_type() -> ValueType {
        <T as IntoValue>::value_type()
    }
    fn into_outcome(self) -> Result<Value, String> {
        match self {
            Ok(v) => Ok(v.into_value()),
            Err(e) => Err(e.to_string()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Array types nest, and their encoding round-trips through the `a`-prefix
    /// form the builtin names and manifest signatures share.
    #[test]
    fn type_codes_round_trip() {
        let cases = [
            (ValueType::Str, "s"),
            (ValueType::Bytes, "y"),
            (ValueType::array_of(ValueType::Str), "as"),
            (ValueType::array_of(ValueType::Bool), "ab"),
            (
                ValueType::array_of(ValueType::array_of(ValueType::Str)),
                "aas",
            ),
        ];
        for (ty, code) in cases {
            assert_eq!(ty.code(), code);
            assert_eq!(ValueType::from_code(code), Some(ty));
        }
        // An `a` with no element, and trailing text, are both rejected.
        assert_eq!(ValueType::from_code("a"), None);
        assert_eq!(ValueType::from_code("si"), None);
    }

    /// The Rust type mapping: `Vec<T>` is `T[]` at any depth; `Bytes` is the
    /// dense `uint8[]`.
    #[test]
    fn rust_types_map_to_value_types() {
        assert_eq!(
            <Vec<String> as FromValue>::value_type(),
            ValueType::array_of(ValueType::Str)
        );
        assert_eq!(
            <Vec<Vec<bool>> as FromValue>::value_type(),
            ValueType::array_of(ValueType::array_of(ValueType::Bool))
        );
        assert_eq!(<Bytes as FromValue>::value_type(), ValueType::Bytes);
    }

    /// A nested array survives the leak/reclaim round trip through `RawValue`.
    #[test]
    fn nested_array_round_trips_through_raw() {
        let v = Value::Array(vec![
            Value::Array(vec![Value::Str("a".into()), Value::Str("b".into())]),
            Value::Array(vec![]),
        ]);
        let raw = v.clone().into_raw();
        assert_eq!(unsafe { Value::from_raw(&raw) }.unwrap(), v);
        unsafe { release_raw(raw) };
    }
}
