//! Native-plugin dispatch: the `pp_plugin_call_{int,float,obj}` runtime
//! symbols behind the `_plugin_[f]call_<t>` builtins the loader synthesizes
//! (see `prepoly_resolve::plugin`).
//!
//! Every call carries the plugin library path, the plugin function name, and
//! the encoded signature as string objects, plus the payload packed into
//! 8-byte slots (integers as i64, bools 0/1, floats as raw bits, heap objects
//! as addresses). The runtime decodes the slots per the signature, marshals
//! through `prepoly_plugin_host` (which shares the front end's `dlopen`
//! cache), and shapes the result:
//!
//! - `_int` returns void/bool/int results in an i64,
//! - `_float` returns an f64,
//! - `_obj` returns a heap object -- a string, a `uint8[]`, a `T[]` (built at
//!   the declared element type's width), or (for the fallible
//!   `_plugin_fcall_*` family) a typed `Result` whose Err payload is the
//!   plugin's error message.
//!
//! Host-contract failures on an infallible call (the library or function
//! disappeared since the program was compiled) cannot produce a value and
//! abort with the message; on a fallible call they surface as a catchable
//! `Err` like any plugin failure.

#[cfg(not(target_family = "wasm"))]
mod real {
    use std::path::Path;

    use prepoly_plugin_host::{CallFailure, Value, ValueType, parse_sig};

    use crate::alloc::{pp_arr_new, pp_str_const, typed_result, typed_result_err, typed_str};
    use crate::builtins::pp_panic_str;
    use crate::rt::Header;

    /// A Prepoly array object's length and element buffer.
    ///
    /// # Safety
    /// `arr` must be a growable-array object (see `crate::alloc`).
    unsafe fn array_parts(arr: *mut Header) -> (usize, *const u8) {
        unsafe {
            let len = *((arr as *const u8).offset(16) as *const i64) as usize;
            let data = *((arr as *const u8).offset(32) as *const *const u8);
            (len, data)
        }
    }

    /// Decode one value of type `t` from its 8-byte argument slot: a scalar in
    /// place, or a heap object by address.
    unsafe fn decode_slot(t: &ValueType, slot: i64) -> Result<Value, String> {
        Ok(match t {
            ValueType::Bool => Value::Bool(slot != 0),
            ValueType::Int => Value::Int(slot),
            ValueType::Float => Value::Float(f64::from_bits(slot as u64)),
            ValueType::Str => {
                Value::Str(unsafe { typed_str(slot as usize as *mut Header) }.to_string())
            }
            ValueType::Bytes => {
                let (len, data) = unsafe { array_parts(slot as usize as *mut Header) };
                Value::Bytes(unsafe { std::slice::from_raw_parts(data, len) }.to_vec())
            }
            ValueType::Array(elem) => {
                Value::Array(unsafe { decode_array(elem, slot as usize as *mut Header) }?)
            }
            ValueType::Void => return Err("void plugin parameter".to_string()),
        })
    }

    /// Decode a Prepoly `T[]` object. An element occupies
    /// `elem.array_elem_size()` bytes: a `bool` one byte, every other scalar
    /// eight, and a heap element its pointer -- which is the same shape an
    /// argument slot has, so each element decodes through `decode_slot`.
    unsafe fn decode_array(elem: &ValueType, arr: *mut Header) -> Result<Vec<Value>, String> {
        let (len, data) = unsafe { array_parts(arr) };
        let size = elem.array_elem_size();
        if size == 0 {
            return Err("array of void plugin elements".to_string());
        }
        (0..len)
            .map(|i| {
                let at = unsafe { data.add(i * size) };
                let slot = match size {
                    1 => i64::from(unsafe { *at }),
                    _ => unsafe { *(at as *const i64) },
                };
                unsafe { decode_slot(elem, slot) }
            })
            .collect()
    }

    /// Decode the packed argument slots per the signature's parameter types.
    unsafe fn decode_args(
        params: &[ValueType],
        argv: *const i64,
        argc: i64,
    ) -> Result<Vec<Value>, String> {
        if params.len() != argc as usize {
            return Err(format!(
                "plugin call passes {argc} argument(s), signature has {}",
                params.len()
            ));
        }
        let slots = if argc == 0 {
            &[]
        } else {
            unsafe { std::slice::from_raw_parts(argv, argc as usize) }
        };
        params
            .iter()
            .zip(slots)
            .map(|(t, &slot)| unsafe { decode_slot(t, slot) })
            .collect()
    }

    /// The shared body: decode the strings and slots, call through the host.
    /// Also returns the declared return type and fallibility for shaping.
    unsafe fn run(
        path: *mut Header,
        name: *mut Header,
        sig: *mut Header,
        argv: *const i64,
        argc: i64,
    ) -> (Result<Value, CallFailure>, ValueType, bool) {
        let (path, name, sig) = unsafe { (typed_str(path), typed_str(name), typed_str(sig)) };
        let (params, ret, fallible) = match parse_sig(sig) {
            Ok(decoded) => decoded,
            Err(e) => return (Err(CallFailure::Host(e)), ValueType::Void, false),
        };
        let args = match unsafe { decode_args(&params, argv, argc) } {
            Ok(args) => args,
            Err(e) => return (Err(CallFailure::Host(e)), ret, fallible),
        };
        (
            prepoly_plugin_host::call(Path::new(path), name, &args),
            ret,
            fallible,
        )
    }

    /// A returned value's scalar encoding (the `_int` family).
    fn scalar(v: &Value) -> i64 {
        match v {
            Value::Void => 0,
            Value::Bool(b) => i64::from(*b),
            Value::Int(i) => *i,
            other => pp_panic_str(&format!(
                "plugin returned {other:?} where a scalar was typed"
            )),
        }
    }

    /// A returned string, byte buffer, or array as a heap object. `ret` is the
    /// declared type: an empty array carries no element type of its own, and
    /// the element type fixes the buffer's element size.
    unsafe fn heap_payload(v: Value, ret: &ValueType) -> *mut Header {
        match (v, ret) {
            (Value::Str(s), _) => unsafe { pp_str_const(s.as_ptr(), s.len() as i64) },
            (Value::Bytes(b), _) => unsafe {
                let arr = pp_arr_new(1, b.len() as i64);
                let data = *((arr as *mut u8).offset(32) as *mut *mut u8);
                std::ptr::copy_nonoverlapping(b.as_ptr(), data, b.len());
                arr
            },
            (Value::Array(items), ValueType::Array(elem)) => unsafe { build_array(items, elem) },
            (other, _) => pp_panic_str(&format!(
                "plugin returned {other:?} where an object was typed"
            )),
        }
    }

    /// Build a Prepoly `T[]` from returned elements, storing each at the
    /// element type's width (mirroring the typed back end's array layout: a
    /// `bool` one byte, another scalar eight, a heap element its pointer).
    unsafe fn build_array(items: Vec<Value>, elem: &ValueType) -> *mut Header {
        let size = elem.array_elem_size();
        if size == 0 {
            pp_panic_str("plugin returned an array of void elements");
        }
        unsafe {
            let arr = pp_arr_new(size as i64, items.len() as i64);
            let data = *((arr as *mut u8).offset(32) as *mut *mut u8);
            for (i, v) in items.into_iter().enumerate() {
                let at = data.add(i * size);
                match elem {
                    ValueType::Bool => *at = u8::from(scalar(&v) != 0),
                    ValueType::Int => *(at as *mut i64) = scalar(&v),
                    ValueType::Float => match v {
                        Value::Float(f) => *(at as *mut f64) = f,
                        ref other => pp_panic_str(&format!(
                            "plugin returned {other:?} where a float element was typed"
                        )),
                    },
                    _ => *(at as *mut *mut Header) = heap_payload(v, elem),
                }
            }
            arr
        }
    }

    /// # Safety
    /// The string operands must be string objects and `argv` must hold `argc`
    /// slots matching the signature (generated code guarantees both).
    pub unsafe extern "C-unwind" fn pp_plugin_call_int(
        path: *mut Header,
        name: *mut Header,
        sig: *mut Header,
        argv: *const i64,
        argc: i64,
    ) -> i64 {
        match unsafe { run(path, name, sig, argv, argc) }.0 {
            Ok(v) => scalar(&v),
            Err(f) => pp_panic_str(f.message()),
        }
    }

    /// # Safety
    /// See [`pp_plugin_call_int`].
    pub unsafe extern "C-unwind" fn pp_plugin_call_float(
        path: *mut Header,
        name: *mut Header,
        sig: *mut Header,
        argv: *const i64,
        argc: i64,
    ) -> f64 {
        match unsafe { run(path, name, sig, argv, argc) }.0 {
            Ok(Value::Float(f)) => f,
            Ok(other) => pp_panic_str(&format!(
                "plugin returned {other:?} where a float was typed"
            )),
            Err(f) => pp_panic_str(f.message()),
        }
    }

    /// # Safety
    /// See [`pp_plugin_call_int`].
    pub unsafe extern "C-unwind" fn pp_plugin_call_obj(
        path: *mut Header,
        name: *mut Header,
        sig: *mut Header,
        argv: *const i64,
        argc: i64,
    ) -> *mut Header {
        let (outcome, ret, fallible) = unsafe { run(path, name, sig, argv, argc) };
        if !fallible {
            return match outcome {
                Ok(v) => unsafe { heap_payload(v, &ret) },
                Err(f) => pp_panic_str(f.message()),
            };
        }
        match outcome {
            Ok(v) => unsafe {
                typed_result(true, |p| match ret {
                    ValueType::Void => *(p as *mut i64) = 0,
                    ValueType::Bool | ValueType::Int => *(p as *mut i64) = scalar(&v),
                    ValueType::Float => match v {
                        Value::Float(f) => *(p as *mut f64) = f,
                        ref other => pp_panic_str(&format!(
                            "plugin returned {other:?} where a float was typed"
                        )),
                    },
                    ValueType::Str | ValueType::Bytes | ValueType::Array(_) => {
                        *(p as *mut *mut Header) = heap_payload(v, &ret)
                    }
                })
            },
            // A fallible call surfaces every failure -- the plugin's own error
            // or a host-contract break -- as a catchable `Err`.
            Err(f) => unsafe { typed_result_err(f.message()) },
        }
    }
}

#[cfg(not(target_family = "wasm"))]
pub use real::{pp_plugin_call_float, pp_plugin_call_int, pp_plugin_call_obj};

// Wasm targets cannot load native plugins (the front end already refuses the
// import); the symbols exist so the table in `lib.rs` compiles unchanged.
#[cfg(target_family = "wasm")]
mod stub {
    use crate::builtins::pp_panic_str;
    use crate::rt::Header;

    fn unsupported() -> ! {
        pp_panic_str("native plugins are not supported by this runtime")
    }

    /// # Safety
    /// Never returns.
    pub unsafe extern "C-unwind" fn pp_plugin_call_int(
        _path: *mut Header,
        _name: *mut Header,
        _sig: *mut Header,
        _argv: *const i64,
        _argc: i64,
    ) -> i64 {
        unsupported()
    }

    /// # Safety
    /// Never returns.
    pub unsafe extern "C-unwind" fn pp_plugin_call_float(
        _path: *mut Header,
        _name: *mut Header,
        _sig: *mut Header,
        _argv: *const i64,
        _argc: i64,
    ) -> f64 {
        unsupported()
    }

    /// # Safety
    /// Never returns.
    pub unsafe extern "C-unwind" fn pp_plugin_call_obj(
        _path: *mut Header,
        _name: *mut Header,
        _sig: *mut Header,
        _argv: *const i64,
        _argc: i64,
    ) -> *mut Header {
        unsupported()
    }
}

#[cfg(target_family = "wasm")]
pub use stub::{pp_plugin_call_float, pp_plugin_call_int, pp_plugin_call_obj};
