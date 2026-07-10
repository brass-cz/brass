//! Host side of Prepoly's native plugin ABI (see the `prepoly_plugin` crate
//! for the plugin side and the ABI contract).
//!
//! Loading is process-global and cached by canonical library path: the front
//! end reads a plugin's manifest while resolving an `import`, and the runtime
//! later calls into the same loaded library, sharing one `dlopen` handle. A
//! loaded plugin stays loaded for the life of the process (unloading a
//! library whose code may still be referenced is never safe).
//!
//! Calling `load_manifest` runs the plugin's registration code, so resolving
//! an import of a plugin executes it — the same trust boundary as running
//! the program that imports it.

use std::path::{Path, PathBuf};
use std::sync::Arc;

pub use prepoly_plugin::{Bytes, Value, ValueType};

/// One function a loaded plugin exposes, decoded from its manifest.
#[derive(Clone, Debug)]
pub struct PluginFunction {
    pub name: String,
    /// The Rust doc comment (markdown prose), when the plugin recorded one.
    pub doc: Option<String>,
    /// Parameter names and types, in call order.
    pub params: Vec<(String, ValueType)>,
    pub ret: ValueType,
    /// Whether the function can fail (Prepoly `-> T!`).
    pub fallible: bool,
    /// The plugin-side dispatch index.
    pub index: u32,
}

/// A loaded plugin's function table.
#[derive(Debug, Default)]
pub struct PluginManifest {
    pub functions: Vec<PluginFunction>,
}

impl PluginManifest {
    pub fn function(&self, name: &str) -> Option<&PluginFunction> {
        self.functions.iter().find(|f| f.name == name)
    }
}

/// Why a plugin call did not produce a value.
#[derive(Debug)]
pub enum CallFailure {
    /// The plugin function reported an error (a fallible function's `Err`,
    /// or a panic inside the plugin). Surfaces as a Prepoly `Result` error.
    Plugin(String),
    /// The host/plugin contract broke (library missing, function missing,
    /// arity drift after a rebuild). A bug or a stale binary, not a value.
    Host(String),
}

impl CallFailure {
    pub fn message(&self) -> &str {
        match self {
            CallFailure::Plugin(m) | CallFailure::Host(m) => m,
        }
    }
}

/// Load (or fetch the cached) manifest of the plugin library at `path`.
pub fn load_manifest(path: &Path) -> Result<Arc<PluginManifest>, String> {
    imp::load(path).map(|p| p.manifest.clone())
}

/// Call `name` in the plugin library at `path`. `args` must match the
/// manifest's parameter list (the compiled program guarantees this; drift
/// after a plugin rebuild reports a [`CallFailure::Host`]).
pub fn call(path: &Path, name: &str, args: &[Value]) -> Result<Value, CallFailure> {
    imp::call(path, name, args)
}

/// Decode a signature string (`"ii:i!"`, as carried by the manifest and by
/// the loader's synthesized call sites) into parameter types, the return
/// type, and fallibility. Type codes are self-delimiting (`a` prefixes each
/// array level), so the parameter list needs no separators.
pub fn parse_sig(sig: &str) -> Result<(Vec<ValueType>, ValueType, bool), String> {
    let (params, ret) = sig
        .split_once(':')
        .ok_or_else(|| format!("malformed signature `{sig}`"))?;
    let mut chars = params.chars();
    let mut param_types = Vec::new();
    while chars.clone().next().is_some() {
        let ty = ValueType::parse(&mut chars)
            .ok_or_else(|| format!("malformed parameter type in `{sig}`"))?;
        param_types.push(ty);
    }
    let fallible = ret.ends_with('!');
    let ret = ret.strip_suffix('!').unwrap_or(ret);
    let ret =
        ValueType::from_code(ret).ok_or_else(|| format!("malformed return type in `{sig}`"))?;
    Ok((param_types, ret, fallible))
}

#[cfg(not(target_family = "wasm"))]
mod imp {
    use std::collections::HashMap;
    use std::path::{Path, PathBuf};
    use std::sync::{Arc, Mutex, OnceLock};

    use prepoly_plugin::raw::{
        ABI_VERSION, CALL_ERR, CALL_OK, RawManifest, RawValue, TAG_ARRAY, TAG_BOOL, TAG_BYTES,
        TAG_FLOAT, TAG_INT, TAG_STRING,
    };
    use prepoly_plugin::{Value, ValueType};

    use crate::{CallFailure, PluginFunction, PluginManifest};

    type EntryFn = unsafe extern "C" fn(u32) -> *const RawManifest;
    type CallFn = unsafe extern "C" fn(u32, *const RawValue, usize, *mut RawValue) -> i32;
    type ReleaseFn = unsafe extern "C" fn(RawValue);

    pub(crate) struct Loaded {
        /// Keeps the library mapped; never dropped (see the module doc).
        lib: libloading::Library,
        pub(crate) manifest: Arc<PluginManifest>,
        by_name: HashMap<String, u32>,
    }

    fn cache() -> &'static Mutex<HashMap<PathBuf, Arc<Loaded>>> {
        static CACHE: OnceLock<Mutex<HashMap<PathBuf, Arc<Loaded>>>> = OnceLock::new();
        CACHE.get_or_init(|| Mutex::new(HashMap::new()))
    }

    pub(crate) fn load(path: &Path) -> Result<Arc<Loaded>, String> {
        let canonical = path
            .canonicalize()
            .map_err(|e| format!("cannot load plugin `{}`: {e}", path.display()))?;
        let mut cache = cache().lock().unwrap();
        if let Some(loaded) = cache.get(&canonical) {
            return Ok(loaded.clone());
        }
        let loaded = Arc::new(load_uncached(&canonical)?);
        cache.insert(canonical, loaded.clone());
        Ok(loaded)
    }

    fn load_uncached(path: &Path) -> Result<Loaded, String> {
        let lib = unsafe { libloading::Library::new(path) }
            .map_err(|e| format!("cannot load plugin `{}`: {e}", path.display()))?;
        let manifest = unsafe {
            let entry: libloading::Symbol<EntryFn> = lib.get(b"prepoly_entry\0").map_err(|e| {
                format!(
                    "`{}` is not a Prepoly plugin (no `prepoly_entry`): {e}",
                    path.display()
                )
            })?;
            let raw = entry(ABI_VERSION);
            if raw.is_null() {
                return Err(format!(
                    "plugin `{}` does not speak plugin ABI v{ABI_VERSION}; rebuild it against \
                     this prepoly_plugin version",
                    path.display()
                ));
            }
            decode_manifest(&*raw, path)?
        };
        let by_name = manifest
            .functions
            .iter()
            .map(|f| (f.name.clone(), f.index))
            .collect();
        Ok(Loaded {
            lib,
            manifest: Arc::new(manifest),
            by_name,
        })
    }

    /// Copy the plugin-owned manifest into host-owned data.
    ///
    /// # Safety-relevant contract
    /// `raw` was produced by a plugin that accepted our ABI version, so its
    /// layout and the lifetimes of the strings it references are trusted.
    unsafe fn decode_manifest(raw: &RawManifest, path: &Path) -> Result<PluginManifest, String> {
        if raw.abi != ABI_VERSION {
            return Err(format!(
                "plugin `{}` speaks plugin ABI v{}, this host v{ABI_VERSION}",
                path.display(),
                raw.abi
            ));
        }
        let fns = if raw.fn_count == 0 {
            &[]
        } else {
            unsafe { std::slice::from_raw_parts(raw.fns, raw.fn_count) }
        };
        let mut functions = Vec::with_capacity(fns.len());
        for f in fns {
            let name = unsafe { f.name.as_str() }.to_string();
            let sig = unsafe { f.sig.as_str() };
            let (types, ret, fallible) = crate::parse_sig(sig)
                .map_err(|e| format!("plugin `{}`, function `{name}`: {e}", path.display()))?;
            let names = unsafe { f.param_names.as_str() };
            let mut names = names.split(',').filter(|s| !s.is_empty());
            let params: Vec<(String, ValueType)> = types
                .into_iter()
                .enumerate()
                .map(|(i, t)| {
                    let n = names.next().map(str::to_string);
                    (n.unwrap_or_else(|| format!("a{i}")), t)
                })
                .collect();
            let doc = unsafe { f.doc.as_str() };
            functions.push(PluginFunction {
                name,
                doc: (!doc.is_empty()).then(|| doc.to_string()),
                params,
                ret,
                fallible,
                index: f.index,
            });
        }
        Ok(PluginManifest { functions })
    }

    /// Encode a call argument, borrowing any string/byte buffer from `v` (the
    /// caller keeps `args` alive across the call). An array argument
    /// additionally needs a contiguous `RawValue` array, which has no home in
    /// `v`; it is built in `keeper`, which the caller likewise keeps alive.
    /// Moving a `Box<[RawValue]>` into `keeper` does not move its heap buffer,
    /// so the recorded pointer stays valid.
    fn arg_raw(v: &Value, keeper: &mut Vec<Box<[RawValue]>>) -> RawValue {
        let mut out = RawValue::void();
        match v {
            Value::Void => {}
            Value::Bool(b) => {
                out.tag = TAG_BOOL;
                out.int = i64::from(*b);
            }
            Value::Int(i) => {
                out.tag = TAG_INT;
                out.int = *i;
            }
            Value::Float(f) => {
                out.tag = TAG_FLOAT;
                out.float = *f;
            }
            Value::Str(s) => {
                out.tag = TAG_STRING;
                out.ptr = s.as_ptr();
                out.len = s.len();
            }
            Value::Bytes(b) => {
                out.tag = TAG_BYTES;
                out.ptr = b.as_ptr();
                out.len = b.len();
            }
            Value::Array(items) => {
                let elems: Box<[RawValue]> = items
                    .iter()
                    .map(|e| arg_raw(e, keeper))
                    .collect::<Vec<_>>()
                    .into();
                out.tag = TAG_ARRAY;
                out.len = elems.len();
                out.ptr = elems.as_ptr() as *const u8;
                keeper.push(elems);
            }
        }
        out
    }

    pub(crate) fn call(path: &Path, name: &str, args: &[Value]) -> Result<Value, CallFailure> {
        let loaded = load(path).map_err(CallFailure::Host)?;
        let Some(&index) = loaded.by_name.get(name) else {
            return Err(CallFailure::Host(format!(
                "plugin `{}` exposes no function `{name}` (was it rebuilt since this program \
                 was compiled?)",
                path.display()
            )));
        };
        // `keeper` owns the element arrays an array argument points at; it
        // must outlive the call.
        let mut keeper: Vec<Box<[RawValue]>> = Vec::new();
        let raw_args: Vec<RawValue> = args.iter().map(|a| arg_raw(a, &mut keeper)).collect();
        let mut out = RawValue::void();
        let status = unsafe {
            let call: libloading::Symbol<CallFn> = loaded
                .lib
                .get(b"prepoly_call\0")
                .map_err(|e| CallFailure::Host(format!("plugin `{}`: {e}", path.display())))?;
            call(index, raw_args.as_ptr(), raw_args.len(), &mut out)
        };
        match status {
            CALL_OK | CALL_ERR => {
                // Copy the plugin-owned result, then hand its buffer back.
                let value = unsafe { Value::from_raw(&out) };
                unsafe {
                    if let Ok(release) = loaded.lib.get::<ReleaseFn>(b"prepoly_release\0") {
                        release(out);
                    }
                }
                let value = value.map_err(CallFailure::Host)?;
                if status == CALL_OK {
                    Ok(value)
                } else {
                    let msg = match value {
                        Value::Str(s) => s,
                        other => format!("{other:?}"),
                    };
                    Err(CallFailure::Plugin(msg))
                }
            }
            _ => Err(CallFailure::Host(format!(
                "plugin `{}`, function `{name}`: call contract violated (status {status}); \
                 the plugin binary likely changed since this program was compiled",
                path.display()
            ))),
        }
    }
}

#[cfg(target_family = "wasm")]
mod imp {
    use std::path::Path;
    use std::sync::Arc;

    use prepoly_plugin::Value;

    use crate::{CallFailure, PluginManifest};

    pub(crate) struct Loaded {
        pub(crate) manifest: Arc<PluginManifest>,
    }

    pub(crate) fn load(_path: &Path) -> Result<Arc<Loaded>, String> {
        Err("native plugins are not supported on this platform".to_string())
    }

    pub(crate) fn call(_path: &Path, _name: &str, _args: &[Value]) -> Result<Value, CallFailure> {
        Err(CallFailure::Host(
            "native plugins are not supported on this platform".to_string(),
        ))
    }
}

/// The platform file names a plugin module `name` may live under, in probe
/// order: `name.so` (explicit) then the `cdylib` output name `libname.so`
/// (`.dylib`/`.dll` per platform).
pub fn library_file_names(name: &str) -> Vec<String> {
    let suffix = std::env::consts::DLL_SUFFIX;
    let prefix = std::env::consts::DLL_PREFIX;
    let mut names = vec![format!("{name}{suffix}")];
    if !prefix.is_empty() {
        names.push(format!("{prefix}{name}{suffix}"));
    }
    names
}

/// Locate the plugin library for module segment `name` under `dir`, if any.
pub fn find_library(dir: &Path, name: &str) -> Option<PathBuf> {
    library_file_names(name)
        .into_iter()
        .map(|f| dir.join(f))
        .find(|p| p.is_file())
}

/// Test support: build the workspace's own plugin cdylibs on demand. Only for
/// the workspace's test suites, which cannot depend on a prior `cargo build`
/// or on `libraries/build.sh` having been run.
#[cfg(feature = "fixture")]
pub mod fixture {
    use std::path::{Path, PathBuf};

    /// The workspace root, from this crate's manifest directory.
    pub fn workspace_root() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(|p| p.parent())
            .expect("workspace root")
            .to_path_buf()
    }

    /// Build workspace package `package` (debug) and return the path of the
    /// cdylib it produces, whose `[lib] name` is `lib_name`.
    pub fn build_plugin(package: &str, lib_name: &str) -> PathBuf {
        let ws_root = workspace_root();
        let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
        let status = std::process::Command::new(cargo)
            .args(["build", "-p", package])
            .current_dir(&ws_root)
            .status()
            .unwrap_or_else(|e| panic!("run cargo build for `{package}`: {e}"));
        assert!(status.success(), "plugin `{package}` failed to build");
        let file = format!(
            "{}{lib_name}{}",
            std::env::consts::DLL_PREFIX,
            std::env::consts::DLL_SUFFIX
        );
        let path = ws_root.join("target").join("debug").join(file);
        assert!(path.is_file(), "plugin not at {}", path.display());
        path
    }

    /// Build `package` and install its cdylib into `dir` under the plain
    /// module name (`process.so`), the name a Prepoly `import` resolves.
    /// Mirrors `libraries/build.sh`, for suites that run before it has.
    pub fn install_plugin(package: &str, lib_name: &str, dir: &Path) -> PathBuf {
        let built = build_plugin(package, lib_name);
        let dest = dir.join(format!("{lib_name}{}", std::env::consts::DLL_SUFFIX));
        std::fs::create_dir_all(dir).expect("create the plugin directory");
        std::fs::copy(&built, &dest).expect("install the plugin");
        dest
    }

    /// Build the fixture plugin the plugin tests load.
    pub fn build_testlib() -> PathBuf {
        build_plugin("prepoly_plugin_testlib", "prepoly_plugin_testlib")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Signature decoding accepts every type code and the fallible marker,
    /// and rejects malformed strings.
    #[test]
    fn signature_decoding() {
        assert_eq!(
            parse_sig("ii:i").unwrap(),
            (vec![ValueType::Int, ValueType::Int], ValueType::Int, false)
        );
        assert_eq!(
            parse_sig("sy:v!").unwrap(),
            (
                vec![ValueType::Str, ValueType::Bytes],
                ValueType::Void,
                true
            )
        );
        assert_eq!(parse_sig(":f").unwrap(), (vec![], ValueType::Float, false));
        assert!(parse_sig("i").is_err());
        assert!(parse_sig("q:i").is_err());
        assert!(parse_sig("i:").is_err());
    }

    /// Array codes are self-delimiting (`a` per level), so an unseparated
    /// parameter list of nested arrays decodes unambiguously; arrays are
    /// ordinary types, usable as returns too.
    #[test]
    fn array_signature_decoding() {
        let str_arr = ValueType::array_of(ValueType::Str);
        assert_eq!(
            parse_sig("assaab:as").unwrap(),
            (
                vec![
                    str_arr.clone(),
                    ValueType::Str,
                    ValueType::array_of(ValueType::array_of(ValueType::Bool)),
                ],
                str_arr,
                false
            )
        );
        // A dangling array marker has no element type.
        assert!(parse_sig("a:i").is_err());
        assert!(parse_sig("i:a").is_err());
    }
}
