//! Host side of Brass's native plugin ABI (see the `brass_plugin` crate
//! for the plugin side and the ABI contract).
//!
//! Loading is process-global and cached by library path: the front end reads a
//! plugin's manifest while resolving an `import`, and the runtime later calls
//! into the same loaded library, sharing one `dlopen` handle. A loaded plugin
//! stays loaded for the life of the process (unloading a library whose code may
//! still be referenced is never safe), including one a rebuild superseded.
//!
//! The two roles treat the cache differently, deliberately:
//!
//! - [`load_manifest`] (front end) revalidates against the file, so a language
//!   server or REPL that outlives a `std/build.sh` sees the new functions.
//! - [`call`] (runtime) pins: after the first load it never touches the
//!   filesystem again, so a running program survives the `.so` being rebuilt or
//!   deleted underneath it, and keeps the code it was compiled against.
//!
//! Calling `load_manifest` runs the plugin's registration code, so resolving
//! an import of a plugin executes it -- the same trust boundary as running
//! the program that imports it.

use std::path::{Path, PathBuf};
use std::sync::Arc;

pub use brass_plugin::{Bytes, Value, ValueType};

/// One function a loaded plugin exposes, decoded from its manifest.
#[derive(Clone, Debug)]
pub struct PluginFunction {
    pub name: String,
    /// The Rust doc comment (markdown prose), when the plugin recorded one.
    pub doc: Option<String>,
    /// Parameter names and types, in call order.
    pub params: Vec<(String, ValueType)>,
    pub ret: ValueType,
    /// Whether the function can fail (Brass `-> T!`).
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
    /// or a panic inside the plugin). Surfaces as a Brass `Result` error.
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

/// The manifest of the plugin library at `path`, revalidated against the file.
///
/// The front end's entry point. A library rebuilt since it was last read is
/// loaded again, so a long-lived process (the language server, a REPL session)
/// never reports a stale function list. Contrast [`call`], which pins.
pub fn load_manifest(path: &Path) -> Result<Arc<PluginManifest>, String> {
    imp::load_fresh(path).map(|p| p.manifest.clone())
}

/// Call `name` in the plugin library at `path`. `args` must match the
/// manifest's parameter list (the compiled program guarantees this; drift
/// after a plugin rebuild reports a [`CallFailure::Host`]).
///
/// The library is pinned: after the first load, the cache answers by the path
/// as given, without touching the filesystem. A running program therefore
/// keeps calling the code it was compiled against even if the file is deleted
/// or rebuilt. Contrast [`load_manifest`], which revalidates.
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
        if contains_void(&ty) {
            return Err(format!("void is not a valid parameter type in `{sig}`"));
        }
        param_types.push(ty);
    }
    let fallible = ret.ends_with('!');
    let ret = ret.strip_suffix('!').unwrap_or(ret);
    let ret =
        ValueType::from_code(ret).ok_or_else(|| format!("malformed return type in `{sig}`"))?;
    if matches!(&ret, ValueType::Array(_)) && contains_void(&ret) {
        return Err(format!("void is not a valid array element type in `{sig}`"));
    }
    Ok((param_types, ret, fallible))
}

fn contains_void(ty: &ValueType) -> bool {
    match ty {
        ValueType::Void => true,
        ValueType::Array(elem) => contains_void(elem),
        _ => false,
    }
}

#[cfg(not(target_family = "wasm"))]
mod imp {
    use std::collections::HashMap;
    use std::path::{Path, PathBuf};
    use std::sync::{Arc, Mutex, OnceLock};

    use brass_plugin::raw::{
        ABI_VERSION, CALL_ERR, CALL_OK, RawManifest, RawValue, TAG_ARRAY, TAG_BOOL, TAG_BYTES,
        TAG_FLOAT, TAG_INT, TAG_STRING,
    };
    use brass_plugin::{Value, ValueType};

    use crate::{CallFailure, PluginFunction, PluginManifest};

    type EntryFn = unsafe extern "C" fn(u32) -> *const RawManifest;
    type CallFn = unsafe extern "C" fn(u32, *const RawValue, usize, *mut RawValue) -> i32;
    type ReleaseFn = unsafe extern "C" fn(RawValue);

    /// What a library file looked like when it was loaded. A rebuild that keeps
    /// both is indistinguishable, which is why only the front end revalidates.
    #[derive(Clone, Copy, PartialEq, Eq)]
    struct Stamp {
        modified: Option<std::time::SystemTime>,
        len: u64,
    }

    fn stamp_of(path: &Path) -> Option<Stamp> {
        std::fs::metadata(path).ok().map(|m| Stamp {
            modified: m.modified().ok(),
            len: m.len(),
        })
    }

    pub(crate) struct Loaded {
        /// Keeps the library mapped; never dropped (see the module doc).
        _lib: libloading::Library,
        pub(crate) manifest: Arc<PluginManifest>,
        by_name: HashMap<String, u32>,
        /// Resolved once: a `dlsym` per call would be pure overhead, and the
        /// library outlives every `Loaded` that names it.
        call: CallFn,
        release: Option<ReleaseFn>,
        stamp: Option<Stamp>,
    }

    #[derive(Default)]
    struct Cache {
        /// Keyed by the path as the caller wrote it AND by its canonical form,
        /// so a repeat call needs no filesystem syscall.
        by_path: HashMap<PathBuf, Arc<Loaded>>,
        /// Entries a `load_manifest` revalidation replaced. Held forever: the
        /// module never unloads a library whose code may still be referenced.
        /// Bounded by the number of rebuilds in one session.
        retired: Vec<Arc<Loaded>>,
    }

    fn cache() -> &'static Mutex<Cache> {
        static CACHE: OnceLock<Mutex<Cache>> = OnceLock::new();
        CACHE.get_or_init(|| Mutex::new(Cache::default()))
    }

    /// The library at `path` for a *running program*: pinned, never revalidated.
    ///
    /// The cache is consulted by the path as given before anything touches the
    /// filesystem, so a program keeps calling the code it was compiled against
    /// even if the `.so` is deleted or rebuilt underneath it. Only the first
    /// load of a path canonicalizes.
    pub(crate) fn load_pinned(path: &Path) -> Result<Arc<Loaded>, String> {
        if let Some(loaded) = cache().lock().unwrap().by_path.get(path) {
            return Ok(loaded.clone());
        }
        let canonical = path
            .canonicalize()
            .map_err(|e| format!("cannot load plugin `{}`: {e}", path.display()))?;
        let mut cache = cache().lock().unwrap();
        let loaded = match cache.by_path.get(&canonical) {
            Some(loaded) => loaded.clone(),
            None => {
                let loaded = Arc::new(load_uncached(&canonical, false)?);
                cache.by_path.insert(canonical.clone(), loaded.clone());
                loaded
            }
        };
        if canonical != path {
            cache.by_path.insert(path.to_path_buf(), loaded.clone());
        }
        Ok(loaded)
    }

    /// The library at `path` for the *front end*: revalidated against the file.
    ///
    /// An editor session or a REPL outlives many rebuilds of the plugin it is
    /// analyzing, and a manifest that predates the current binary reports the
    /// wrong functions. A changed size or mtime therefore reloads, retiring the
    /// old entry (never unloading it) and dropping every path that named it, so
    /// a subsequent [`load_pinned`] pins the new code rather than the old.
    pub(crate) fn load_fresh(path: &Path) -> Result<Arc<Loaded>, String> {
        let canonical = path
            .canonicalize()
            .map_err(|e| format!("cannot load plugin `{}`: {e}", path.display()))?;
        let stamp = stamp_of(&canonical);
        let mut cache = cache().lock().unwrap();
        let mut superseded = false;
        if let Some(loaded) = cache.by_path.get(&canonical) {
            if loaded.stamp == stamp {
                return Ok(loaded.clone());
            }
            let stale = loaded.clone();
            cache.by_path.retain(|_, l| !Arc::ptr_eq(l, &stale));
            cache.retired.push(stale);
            superseded = true;
        }
        let loaded = Arc::new(load_uncached(&canonical, superseded)?);
        cache.by_path.insert(canonical, loaded.clone());
        Ok(loaded)
    }

    /// A path the dynamic loader has not seen, for [`open_library`].
    fn staging_path(of: &Path) -> PathBuf {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let ext = of
            .extension()
            .map(|e| format!(".{}", e.to_string_lossy()))
            .unwrap_or_default();
        std::env::temp_dir().join(format!("brass-plugin-{}-{n}{ext}", std::process::id()))
    }

    /// Open the library at `path`, mapping a `superseded` one through a private
    /// copy.
    ///
    /// `dlopen` resolves an already-loaded object by PATHNAME before it looks at
    /// the file, so re-opening a rebuilt library at the path it replaced hands
    /// back the previous mapping -- whatever the file now holds. Reading a
    /// replacement therefore means opening a copy under a name the loader has
    /// never seen. The copy is unlinked as soon as it is mapped: the mapping
    /// keeps the inode alive, so nothing is left in the temp directory. (Where
    /// an open file cannot be unlinked, the copy simply stays.)
    fn open_library(path: &Path, superseded: bool) -> Result<libloading::Library, String> {
        let fail = |e: std::io::Error| format!("cannot load plugin `{}`: {e}", path.display());
        if !superseded {
            return unsafe { libloading::Library::new(path) }
                .map_err(|e| format!("cannot load plugin `{}`: {e}", path.display()));
        }
        let staged = staging_path(path);
        std::fs::copy(path, &staged).map_err(fail)?;
        let lib = unsafe { libloading::Library::new(&staged) }
            .map_err(|e| format!("cannot load plugin `{}`: {e}", path.display()));
        #[cfg(unix)]
        let _ = std::fs::remove_file(&staged);
        lib
    }

    fn load_uncached(path: &Path, superseded: bool) -> Result<Loaded, String> {
        let stamp = stamp_of(path);
        let lib = open_library(path, superseded)?;
        let manifest = unsafe {
            let entry: libloading::Symbol<EntryFn> = lib.get(b"brass_entry\0").map_err(|e| {
                format!(
                    "`{}` is not a Brass plugin (no `brass_entry`): {e}",
                    path.display()
                )
            })?;
            let raw = entry(ABI_VERSION);
            // A null manifest is the raw ABI's only failure channel: the plugin
            // either refused our version or panicked while registering.
            if raw.is_null() {
                return Err(format!(
                    "plugin `{}` rejected ABI v{ABI_VERSION} or failed to initialize; rebuild it \
                     against this brass_plugin version",
                    path.display()
                ));
            }
            decode_manifest(&*raw, path)?
        };
        // Resolve the call/release entry points once. The pointers stay valid
        // for as long as the library is mapped, which is forever.
        let (call, release) = unsafe {
            let call: libloading::Symbol<CallFn> = lib.get(b"brass_call\0").map_err(|e| {
                format!(
                    "`{}` is not a Brass plugin (no `brass_call`): {e}",
                    path.display()
                )
            })?;
            let release = lib.get::<ReleaseFn>(b"brass_release\0").ok();
            (*call, release.map(|r| *r))
        };
        let by_name = manifest
            .functions
            .iter()
            .map(|f| (f.name.clone(), f.index))
            .collect();
        Ok(Loaded {
            _lib: lib,
            manifest: Arc::new(manifest),
            by_name,
            call,
            release,
            stamp,
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
        let mut functions: Vec<PluginFunction> = Vec::with_capacity(fns.len());
        for f in fns {
            let name = unsafe { f.name.as_str() }.to_string();
            // The loader splices the name into synthesized source; anything
            // that is not an identifier would surface as a parse failure of an
            // invisible module. Duplicates are rejected for the same reason,
            // and because `by_name` below could not name both.
            if !is_ascii_identifier(&name) {
                return Err(format!(
                    "plugin `{}`, function `{name}`: not a legal identifier",
                    path.display()
                ));
            }
            if functions.iter().any(|g: &PluginFunction| g.name == name) {
                return Err(format!(
                    "plugin `{}`: function `{name}` is exported twice",
                    path.display()
                ));
            }
            let sig = unsafe { f.sig.as_str() };
            let (types, ret, fallible) = crate::parse_sig(sig)
                .map_err(|e| format!("plugin `{}`, function `{name}`: {e}", path.display()))?;
            let names = unsafe { f.param_names.as_str() };
            let names: Vec<&str> = if names.is_empty() {
                Vec::new()
            } else {
                names.split(',').collect()
            };
            if names.len() > types.len() {
                return Err(format!(
                    "plugin `{}`, function `{name}`: {} parameter names for {} parameters",
                    path.display(),
                    names.len(),
                    types.len()
                ));
            }
            let mut params: Vec<(String, ValueType)> = Vec::with_capacity(types.len());
            for (i, ty) in types.into_iter().enumerate() {
                let param_name = names
                    .get(i)
                    .filter(|name| !name.is_empty())
                    .map(|name| (*name).to_string())
                    .unwrap_or_else(|| format!("a{i}"));
                if !is_ascii_identifier(&param_name) {
                    return Err(format!(
                        "plugin `{}`, function `{name}`, parameter {i}: `{param_name}` is not a \
                         legal identifier",
                        path.display()
                    ));
                }
                if params.iter().any(|(existing, _)| existing == &param_name) {
                    return Err(format!(
                        "plugin `{}`, function `{name}`: parameter `{param_name}` is declared twice",
                        path.display()
                    ));
                }
                params.push((param_name, ty));
            }
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

    /// `[A-Za-z_][A-Za-z0-9_]*`, the identifier shape both Rust and Brass
    /// accept.
    fn is_ascii_identifier(name: &str) -> bool {
        let mut chars = name.chars();
        chars
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
            && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
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
        let loaded = load_pinned(path).map_err(CallFailure::Host)?;
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
        let status = unsafe { (loaded.call)(index, raw_args.as_ptr(), raw_args.len(), &mut out) };
        match status {
            CALL_OK | CALL_ERR => {
                // Copy the plugin-owned result, then hand its buffer back.
                let value = unsafe { Value::from_raw(&out) };
                if let Some(release) = loaded.release {
                    unsafe { release(out) };
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

    #[cfg(test)]
    mod tests {
        use brass_plugin::raw::{RawFunction, RawManifest, RawStr};

        use super::decode_manifest;

        fn raw_str(s: &'static str) -> RawStr {
            RawStr {
                ptr: s.as_ptr(),
                len: s.len(),
            }
        }

        fn function_with(
            name: &'static str,
            index: u32,
            sig: &'static str,
            param_names: &'static str,
        ) -> RawFunction {
            RawFunction {
                name: raw_str(name),
                doc: raw_str(""),
                sig: raw_str(sig),
                param_names: raw_str(param_names),
                index,
            }
        }

        fn function(name: &'static str, index: u32) -> RawFunction {
            function_with(name, index, ":v", "")
        }

        fn decode(fns: &[RawFunction]) -> Result<Vec<String>, String> {
            let raw = RawManifest {
                abi: brass_plugin::raw::ABI_VERSION,
                fn_count: fns.len(),
                fns: fns.as_ptr(),
            };
            unsafe { decode_manifest(&raw, std::path::Path::new("lib.so")) }
                .map(|m| m.functions.into_iter().map(|f| f.name).collect())
        }

        /// The manifest's names are spliced into synthesized Brass source and
        /// indexed by name, so a name that is not an identifier -- or one
        /// exported twice -- is refused here, where the plugin can be blamed,
        /// rather than surfacing as a parse error in an invisible module.
        #[test]
        fn manifest_names_must_be_unique_identifiers() {
            assert_eq!(
                decode(&[function("ok_name", 0), function("_leading", 1)]).unwrap(),
                vec!["ok_name".to_string(), "_leading".to_string()]
            );

            for bad in ["has space", "with-dash", "9leading", "", "kanji字"] {
                let err = decode(&[function(bad, 0)]).expect_err("rejected");
                assert!(err.contains("not a legal identifier"), "{bad}: {err}");
            }

            let err = decode(&[function("dup", 0), function("dup", 1)]).expect_err("rejected");
            assert!(err.contains("exported twice"), "{err}");
        }

        /// Parameter names become identifiers in synthesized source. Invalid,
        /// duplicate, and surplus names are rejected while omitted slots keep
        /// their stable generated names.
        #[test]
        fn manifest_parameter_names_must_match_source_identifiers() {
            let raw = [function_with("ok", 0, "ii:i", "left,")];
            let manifest = unsafe {
                decode_manifest(
                    &RawManifest {
                        abi: brass_plugin::raw::ABI_VERSION,
                        fn_count: raw.len(),
                        fns: raw.as_ptr(),
                    },
                    std::path::Path::new("lib.so"),
                )
            }
            .unwrap();
            assert_eq!(manifest.functions[0].params[0].0, "left");
            assert_eq!(manifest.functions[0].params[1].0, "a1");

            for names in ["has-dash,right", "same,same", "one,two,three"] {
                let err = decode(&[function_with("bad", 0, "ii:i", names)]).expect_err("rejected");
                assert!(
                    err.contains("legal identifier")
                        || err.contains("declared twice")
                        || err.contains("parameter names"),
                    "{names}: {err}"
                );
            }
        }
    }
}

#[cfg(target_family = "wasm")]
mod imp {
    use std::path::Path;
    use std::sync::Arc;

    use brass_plugin::Value;

    use crate::{CallFailure, PluginManifest};

    pub(crate) struct Loaded {
        pub(crate) manifest: Arc<PluginManifest>,
    }

    pub(crate) fn load_fresh(_path: &Path) -> Result<Arc<Loaded>, String> {
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
/// or on `std/build.sh` having been run.
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
    ///
    /// The artifact path is read from cargo's own JSON output rather than
    /// assumed to be `target/debug`, which a `CARGO_TARGET_DIR` or a
    /// `build.target-dir` config would move.
    pub fn build_plugin(package: &str, lib_name: &str) -> PathBuf {
        let ws_root = workspace_root();
        let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
        let out = std::process::Command::new(cargo)
            .args([
                "build",
                "-p",
                package,
                "--message-format=json-render-diagnostics",
            ])
            .current_dir(&ws_root)
            .output()
            .unwrap_or_else(|e| panic!("run cargo build for `{package}`: {e}"));
        assert!(
            out.status.success(),
            "plugin `{package}` failed to build:\n{}",
            String::from_utf8_lossy(&out.stderr)
        );
        let file = format!(
            "{}{lib_name}{}",
            std::env::consts::DLL_PREFIX,
            std::env::consts::DLL_SUFFIX
        );
        let path = artifact_path(&String::from_utf8_lossy(&out.stdout), &file)
            .unwrap_or_else(|| ws_root.join("target").join("debug").join(&file));
        assert!(path.is_file(), "plugin not at {}", path.display());
        path
    }

    /// The last `compiler-artifact` filename ending in `file` from cargo's
    /// newline-delimited JSON. Parsed by hand: pulling in a JSON dependency for
    /// one field would be paid for by every crate that enables `fixture`.
    fn artifact_path(stdout: &str, file: &str) -> Option<PathBuf> {
        stdout
            .lines()
            .filter(|l| l.contains("\"reason\":\"compiler-artifact\""))
            .flat_map(|l| l.split('"'))
            .filter(|s| s.ends_with(file))
            .map(PathBuf::from)
            .next_back()
    }

    /// Build `package` and install its cdylib into `dir` under the built
    /// library's own file name (`libprocess.so`), the layout
    /// `std/build.sh` produces and a Brass `import libprocess`
    /// resolves. Mirrors the script, for suites that run before it has.
    pub fn install_plugin(package: &str, lib_name: &str, dir: &Path) -> PathBuf {
        let built = build_plugin(package, lib_name);
        let dest = dir.join(format!(
            "{}{lib_name}{}",
            std::env::consts::DLL_PREFIX,
            std::env::consts::DLL_SUFFIX
        ));
        std::fs::create_dir_all(dir).expect("create the plugin directory");
        std::fs::copy(&built, &dest).expect("install the plugin");
        dest
    }

    /// Build the fixture plugin the plugin tests load.
    pub fn build_testlib() -> PathBuf {
        build_plugin("brass_plugin_testlib", "brass_plugin_testlib")
    }

    /// Build the fixture plugin whose registration panics.
    pub fn build_faultylib() -> PathBuf {
        build_plugin("brass_plugin_faultylib", "brass_plugin_faultylib")
    }

    /// Build the fixture plugin that stands in for a rebuilt `build_testlib`.
    pub fn build_altlib() -> PathBuf {
        build_plugin("brass_plugin_altlib", "brass_plugin_altlib")
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
        assert!(parse_sig("v:i").is_err());
        assert!(parse_sig("av:i").is_err());
        assert!(parse_sig(":av").is_err());
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
