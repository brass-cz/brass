//! Author native Brass plugins in Rust.
//!
//! A plugin is a `cdylib` crate. Implement [`BrassLib`] on a marker type,
//! define the functions with [`export!`] (which keeps the Rust doc comment,
//! shown by Brass's editor tooling), register them in `entry`, and expose
//! the library with [`brass_lib!`]:
//!
//! ```
//! use brass_plugin::{decl, export, brass_lib, BrassLib, Registry};
//!
//! export! {
//!     /// Adds two integers.
//!     fn add(a: i64, b: i64) -> i64 { a + b }
//!
//!     /// Divides, failing on a zero divisor.
//!     fn div(a: i64, b: i64) -> Result<i64, String> {
//!         if b == 0 { Err("division by zero".into()) } else { Ok(a / b) }
//!     }
//! }
//!
//! struct MathLib;
//!
//! impl BrassLib for MathLib {
//!     fn entry(reg: &mut Registry) {
//!         reg.export(decl!(add));
//!         reg.export(decl!(div));
//!     }
//! }
//!
//! brass_lib!(MathLib);
//! # fn main() {}
//! ```
//!
//! (`export!` defines items, so it is used at module scope, not inside a
//! function body.)
//!
//! Build with `crate-type = ["cdylib"]` and import from Brass by the
//! library file's path: `import plugins.math.{ add }` loads
//! `plugins/math.so` (or `plugins/libmath.so`, `.dylib`/`.dll` per platform)
//! relative to the importing file.
//!
//! Supported types, as parameters and as returns: `bool`, `i64`, `f64`,
//! `String`, [`Bytes`], and `Vec<T>` of any of them, nesting freely (Brass
//! `bool`, `int64`, `float64`, `string`, `uint8[]`, `T[]` -- so `Vec<String>`
//! is `string[]` and `Vec<Vec<bool>>` is `bool[][]`). A byte buffer is
//! [`Bytes`], not `Vec<u8>`: `Vec<T>` is the general array, and the boundary's
//! only integer is `int64`. Returns additionally allow `()` and
//! `Result<T, impl Display>` -- a `Result` function is fallible in Brass
//! (`-> T!`).
//!
//! The host loads the library and runs its registration when the program (or
//! an editor analyzing it) resolves the import, so a plugin runs with the
//! same trust as the program importing it.

mod handle;
pub mod raw;
mod registry;
mod value;

use std::sync::OnceLock;

pub use handle::{HandleError, HandleTable};
pub use registry::{FunctionDecl, PluginFn, Registry};
pub use value::{Bytes, FromValue, IntoOutcome, IntoValue, Value, ValueType, release_raw};

/// A Brass plugin library: one type per `cdylib`, registering everything
/// the library exposes. Wire it up with [`brass_lib!`].
pub trait BrassLib {
    /// Register every function the library exposes.
    fn entry(reg: &mut Registry);
}

/// Define plugin functions, capturing each one's Rust doc comment and
/// parameter names for Brass's editor tooling. The functions stay ordinary
/// Rust functions; each also gets a hidden declaration that [`decl!`] hands
/// to [`Registry::export`].
#[macro_export]
macro_rules! export {
    ($( $(#[doc = $doc:literal])* $vis:vis fn $name:ident ( $($arg:ident : $aty:ty),* $(,)? ) $(-> $ret:ty)? $body:block )+) => {
        $(
            $(#[doc = $doc])*
            $vis fn $name($($arg: $aty),*) $(-> $ret)? $body

            #[doc(hidden)]
            #[allow(non_snake_case)]
            $vis mod $name {
                #[allow(unused_imports)]
                use super::*;

                pub fn __brass_decl() -> $crate::FunctionDecl {
                    let doc = $crate::__join_doc(&[$($doc),*]);
                    $crate::FunctionDecl::new(
                        stringify!($name),
                        doc,
                        super::$name as fn($($aty),*) $(-> $ret)?,
                    )
                    .with_param_names(&[$(stringify!($arg)),*])
                }
            }
        )+
    };
}

/// The [`FunctionDecl`] of a function defined with [`export!`].
#[macro_export]
macro_rules! decl {
    ($name:ident) => {
        $name::__brass_decl()
    };
}

/// Expose a [`BrassLib`] implementation as this `cdylib`'s Brass entry
/// points (`brass_entry` / `brass_call` / `brass_release`; see
/// [`raw`]). Invoke exactly once per plugin crate.
#[macro_export]
macro_rules! brass_lib {
    ($lib:ty) => {
        #[unsafe(no_mangle)]
        pub extern "C" fn brass_entry(host_abi: u32) -> *const $crate::raw::RawManifest {
            $crate::__entry::<$lib>(host_abi)
        }

        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn brass_call(
            index: u32,
            args: *const $crate::raw::RawValue,
            argc: usize,
            out: *mut $crate::raw::RawValue,
        ) -> i32 {
            unsafe { $crate::__call(index, args, argc, out) }
        }

        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn brass_release(value: $crate::raw::RawValue) {
            unsafe { $crate::__release(value) }
        }
    };
}

/// Join `#[doc]` fragments into the markdown prose of a doc comment: each
/// fragment is one line, with the customary space after `///` stripped.
#[doc(hidden)]
pub fn __join_doc(lines: &[&str]) -> Option<String> {
    if lines.is_empty() {
        return None;
    }
    let text = lines
        .iter()
        .map(|l| l.strip_prefix(' ').unwrap_or(l))
        .collect::<Vec<_>>()
        .join("\n");
    let trimmed = text.trim();
    (!trimmed.is_empty()).then(|| trimmed.to_string())
}

/// The registry plus the leaked manifest it was encoded into. Built once per
/// plugin on the first `brass_entry` call. The manifest address is stored
/// untyped because raw pointers are not `Sync`; it points at leaked (hence
/// `'static`) storage.
struct State {
    decls: Vec<FunctionDecl>,
    manifest: usize,
}

static STATE: OnceLock<State> = OnceLock::new();

fn leak_str(s: &str) -> raw::RawStr {
    let leaked: &'static str = Box::leak(s.to_string().into_boxed_str());
    raw::RawStr {
        ptr: leaked.as_ptr(),
        len: leaked.len(),
    }
}

fn build_state<L: BrassLib>() -> State {
    let mut reg = Registry::new();
    L::entry(&mut reg);
    let fns: Vec<raw::RawFunction> = reg
        .decls
        .iter()
        .enumerate()
        .map(|(i, d)| raw::RawFunction {
            name: leak_str(&d.name),
            doc: leak_str(d.doc.as_deref().unwrap_or("")),
            sig: leak_str(&d.sig_string()),
            param_names: leak_str(&d.param_names.join(",")),
            index: i as u32,
        })
        .collect();
    let fns: &'static [raw::RawFunction] = Box::leak(fns.into_boxed_slice());
    let manifest: &'static raw::RawManifest = Box::leak(Box::new(raw::RawManifest {
        abi: raw::ABI_VERSION,
        fn_count: fns.len(),
        fns: fns.as_ptr(),
    }));
    State {
        decls: reg.decls,
        manifest: manifest as *const _ as usize,
    }
}

#[doc(hidden)]
pub fn __entry<L: BrassLib>(host_abi: u32) -> *const raw::RawManifest {
    // A host speaking a different ABI would misread the manifest; refuse it
    // outright (the host reports "plugin rejected ABI"). The manifest also
    // carries the plugin's version so the host can double-check.
    if host_abi != raw::ABI_VERSION {
        return core::ptr::null();
    }
    // `entry` is arbitrary plugin code reached through the plain `extern "C"`
    // `brass_entry`, and this runs inside the compiler and the language
    // server: a panic escaping here would abort the editor session. Report the
    // failure through the only channel the raw ABI has, a null manifest.
    // `OnceLock::get_or_init` leaves the cell empty when its initializer
    // panics, so a later retry is well defined.
    let state = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        STATE.get_or_init(build_state::<L>)
    }));
    match state {
        Ok(s) => s.manifest as *const raw::RawManifest,
        Err(_) => core::ptr::null(),
    }
}

/// # Safety
/// `args` must point at `argc` live values; `out` must be writable.
#[doc(hidden)]
pub unsafe fn __call(
    index: u32,
    args: *const raw::RawValue,
    argc: usize,
    out: *mut raw::RawValue,
) -> i32 {
    let Some(state) = STATE.get() else {
        return raw::CALL_BAD;
    };
    let Some(decl) = state.decls.get(index as usize) else {
        return raw::CALL_BAD;
    };
    if argc != decl.param_types.len() {
        return raw::CALL_BAD;
    }
    let raws: &[raw::RawValue] = if argc == 0 {
        &[]
    } else {
        unsafe { core::slice::from_raw_parts(args, argc) }
    };
    let mut values = Vec::with_capacity(argc);
    for r in raws {
        match unsafe { Value::from_raw(r) } {
            Ok(v) => values.push(v),
            Err(_) => return raw::CALL_BAD,
        }
    }
    // A panic must not unwind across the C boundary; surface it as a call
    // error the host reports like any other plugin failure.
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| (decl.adapter)(values)))
        .unwrap_or_else(|payload| Err(panic_message(payload)));
    match outcome {
        Ok(v) => {
            unsafe { *out = v.into_raw() };
            raw::CALL_OK
        }
        Err(msg) => {
            unsafe { *out = Value::Str(msg).into_raw() };
            raw::CALL_ERR
        }
    }
}

fn panic_message(payload: Box<dyn std::any::Any + Send>) -> String {
    let msg = payload
        .downcast_ref::<&str>()
        .map(|s| (*s).to_string())
        .or_else(|| payload.downcast_ref::<String>().cloned())
        .unwrap_or_else(|| "unknown panic".to_string());
    format!("plugin function panicked: {msg}")
}

/// # Safety
/// `value` must come from this plugin's `brass_call` output and not have
/// been released before.
#[doc(hidden)]
pub unsafe fn __release(value: raw::RawValue) {
    unsafe { release_raw(value) }
}

#[cfg(test)]
mod tests {
    use super::*;

    export! {
        /// Adds two integers.
        ///
        /// Wraps on overflow.
        fn add(a: i64, b: i64) -> i64 { a.wrapping_add(b) }

        /// Uppercases text.
        fn shout(text: String) -> String { text.to_uppercase() }

        /// Joins strings with a comma.
        fn join(parts: Vec<String>) -> String { parts.join(",") }

        /// Splits on commas.
        fn split(text: String) -> Vec<String> {
            text.split(',').map(str::to_string).collect()
        }

        /// Row lengths of a nested array.
        fn row_lengths(rows: Vec<Vec<String>>) -> Vec<i64> {
            rows.iter().map(|r| r.len() as i64).collect()
        }

        fn no_doc() {}

        /// Fails on zero.
        fn checked(v: i64) -> Result<i64, String> {
            if v == 0 { Err("zero".into()) } else { Ok(v) }
        }
    }

    struct TestLib;

    impl BrassLib for TestLib {
        fn entry(reg: &mut Registry) {
            reg.export(decl!(add));
            reg.export(decl!(shout));
            reg.export(decl!(join));
            reg.export(decl!(split));
            reg.export(decl!(row_lengths));
            reg.export(decl!(no_doc));
            reg.export(decl!(checked));
            reg.function("mul", |a: i64, b: i64| a * b);
        }
    }

    brass_lib!(TestLib);

    fn manifest() -> &'static raw::RawManifest {
        let m = brass_entry(raw::ABI_VERSION);
        assert!(!m.is_null());
        unsafe { &*m }
    }

    /// `export!` keeps the doc comment (joined, `///` space stripped) and the
    /// written parameter names; the signature encodes types and fallibility.
    #[test]
    fn manifest_carries_docs_names_and_signatures() {
        let m = manifest();
        assert_eq!(m.abi, raw::ABI_VERSION);
        let fns = unsafe { core::slice::from_raw_parts(m.fns, m.fn_count) };
        let by_name = |n: &str| {
            fns.iter()
                .find(|f| unsafe { f.name.as_str() } == n)
                .unwrap_or_else(|| panic!("no fn {n}"))
        };

        let add = by_name("add");
        assert_eq!(
            unsafe { add.doc.as_str() },
            "Adds two integers.\n\nWraps on overflow."
        );
        assert_eq!(unsafe { add.sig.as_str() }, "ii:i");
        assert_eq!(unsafe { add.param_names.as_str() }, "a,b");

        assert_eq!(unsafe { by_name("shout").sig.as_str() }, "s:s");
        // Arrays encode as `a` per level, in both directions, and nest.
        assert_eq!(unsafe { by_name("join").sig.as_str() }, "as:s");
        assert_eq!(unsafe { by_name("split").sig.as_str() }, "s:as");
        assert_eq!(unsafe { by_name("row_lengths").sig.as_str() }, "aas:ai");
        assert_eq!(unsafe { by_name("no_doc").doc.as_str() }, "");
        assert_eq!(unsafe { by_name("no_doc").sig.as_str() }, ":v");
        // A `Result` return marks the function fallible.
        assert_eq!(unsafe { by_name("checked").sig.as_str() }, "i:i!");
        // A bare closure registration gets generated parameter names.
        assert_eq!(unsafe { by_name("mul").param_names.as_str() }, "a0,a1");
    }

    fn call(index: u32, args: &[raw::RawValue]) -> (i32, raw::RawValue) {
        let mut out = raw::RawValue::void();
        let status = unsafe { brass_call(index, args.as_ptr(), args.len(), &mut out) };
        (status, out)
    }

    fn int(v: i64) -> raw::RawValue {
        Value::Int(v).into_raw()
    }

    /// Calls dispatch by manifest index, convert arguments, and encode the
    /// result; errors and arity mismatches report distinct statuses.
    #[test]
    fn calls_dispatch_and_report_errors() {
        let m = manifest();
        let fns = unsafe { core::slice::from_raw_parts(m.fns, m.fn_count) };
        let index_of = |n: &str| {
            fns.iter()
                .find(|f| unsafe { f.name.as_str() } == n)
                .unwrap()
                .index
        };

        let (status, out) = call(index_of("add"), &[int(2), int(40)]);
        assert_eq!((status, out.tag, out.int), (raw::CALL_OK, raw::TAG_INT, 42));

        // A string result crosses as a plugin-owned buffer, released after copy.
        let (status, out) = call(index_of("shout"), &[Value::Str("hey".into()).into_raw()]);
        assert_eq!(status, raw::CALL_OK);
        let got = unsafe { Value::from_raw(&out) }.unwrap();
        assert_eq!(got, Value::Str("HEY".into()));
        unsafe { brass_release(out) };

        // Arrays cross in both directions, and nest.
        let strings = Value::Array(vec![Value::Str("a".into()), Value::Str("b".into())]).into_raw();
        let (status, out) = call(index_of("join"), &[strings]);
        assert_eq!(status, raw::CALL_OK);
        assert_eq!(
            unsafe { Value::from_raw(&out) }.unwrap(),
            Value::Str("a,b".into())
        );
        unsafe { brass_release(out) };
        unsafe { release_raw(strings) };

        let (status, out) = call(index_of("split"), &[Value::Str("x,y".into()).into_raw()]);
        assert_eq!(status, raw::CALL_OK);
        assert_eq!(
            unsafe { Value::from_raw(&out) }.unwrap(),
            Value::Array(vec![Value::Str("x".into()), Value::Str("y".into())])
        );
        unsafe { brass_release(out) };

        let rows = Value::Array(vec![
            Value::Array(vec![Value::Str("a".into())]),
            Value::Array(vec![]),
        ])
        .into_raw();
        let (status, out) = call(index_of("row_lengths"), &[rows]);
        assert_eq!(status, raw::CALL_OK);
        assert_eq!(
            unsafe { Value::from_raw(&out) }.unwrap(),
            Value::Array(vec![Value::Int(1), Value::Int(0)])
        );
        unsafe { brass_release(out) };
        unsafe { release_raw(rows) };

        // A fallible function's Err surfaces as CALL_ERR with the message.
        let (status, out) = call(index_of("checked"), &[int(0)]);
        assert_eq!(status, raw::CALL_ERR);
        assert_eq!(
            unsafe { Value::from_raw(&out) }.unwrap(),
            Value::Str("zero".into())
        );
        unsafe { brass_release(out) };

        // Wrong arity is a contract violation, not a plugin error.
        let (status, _) = call(index_of("add"), &[int(1)]);
        assert_eq!(status, raw::CALL_BAD);
    }

    /// A wrong-ABI host is refused at entry.
    #[test]
    fn abi_mismatch_is_refused() {
        assert!(brass_entry(raw::ABI_VERSION + 1).is_null());
    }
}
