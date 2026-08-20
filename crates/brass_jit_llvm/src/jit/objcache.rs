//! Versioned native-object packfiles for lazy ORC groups.
//!
//! Each pack is bound to the serialized analysis-cache body that produced the
//! monomorphized program and to the complete native target identity. Groups
//! carry their full ordered public-symbol list as an additional structural
//! guard: a stable first-symbol key alone must never revive an object after the
//! grouping algorithm or reachable instance set changes. A group also records
//! the module `_PATH` values its code embeds, so relocating a project only
//! invalidates the objects whose constants actually changed.

use std::collections::HashMap;
use std::ffi::CStr;
use std::path::{Path, PathBuf};

use llvm_sys::core::LLVMDisposeMessage;
use llvm_sys::target_machine::LLVMGetDefaultTargetTriple;

use super::orc::{OptTier, target_cpu_identity};

const OBJECT_PACK_FORMAT_VERSION: u16 = 2;
const MODULE_PATH_CONST: &str = "_PATH";

type CurrentModulePaths = HashMap<Vec<String>, String>;
type CachedGroups = HashMap<String, CachedObject>;

#[derive(Clone, Debug, Eq, Hash, PartialEq, serde::Serialize, serde::Deserialize)]
pub(crate) struct ModulePathBinding {
    module: Vec<String>,
    value: String,
}

#[derive(Clone, Debug, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
struct PackedGroup {
    key: String,
    symbols: Vec<String>,
    path_bindings: Vec<ModulePathBinding>,
    object: Vec<u8>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CachedObject {
    symbols: Vec<String>,
    path_bindings: Vec<ModulePathBinding>,
    object: Vec<u8>,
}

pub(crate) struct GroupMetadata {
    pub(crate) symbols: Vec<String>,
    pub(crate) path_bindings: Vec<ModulePathBinding>,
}

#[derive(Clone, Debug, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
struct ObjectPack {
    analysis_hash: [u8; 20],
    triple: String,
    cpu: String,
    features: String,
    groups: Vec<PackedGroup>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TargetIdentity {
    triple: String,
    cpu: String,
    features: String,
}

/// Native objects whose header, analysis identity, and target identity have
/// already been validated. The driver may pass this opaque value into the JIT;
/// group-level symbol validation remains the code generator's responsibility.
pub struct ValidatedObjects {
    groups: CachedGroups,
}

impl ValidatedObjects {
    pub(crate) fn matching_object(&self, key: &str, symbols: &[String]) -> Option<&[u8]> {
        let cached = self.groups.get(key)?;
        (cached.symbols == symbols).then_some(cached.object.as_slice())
    }
}

/// Current logical-module to `_PATH` bindings, read from the injected module
/// constants after analysis-cache re-anchoring.
pub(crate) fn module_path_bindings(program: &brass_hir::Program) -> Vec<ModulePathBinding> {
    use brass_parser::ast::{Expr, Pattern, Stmt, StrSeg};

    let mut bindings: Vec<_> = program
        .inits
        .iter()
        .filter_map(|init| {
            let value = init.stmts.iter().find_map(|stmt| match stmt {
                Stmt::Let {
                    pat: Pattern::Binding(name, _),
                    value: Some(Expr::Str(segments, _)),
                    is_const: true,
                    ..
                } if name == MODULE_PATH_CONST => match segments.as_slice() {
                    [StrSeg::Lit(value)] => Some(value.clone()),
                    _ => None,
                },
                _ => None,
            })?;
            Some(ModulePathBinding {
                module: init.path.clone(),
                value,
            })
        })
        .collect();
    bindings.sort_by(|left, right| left.module.cmp(&right.module));
    bindings
}

/// The `_PATH` constants emitted by this exact lazy group. Module initializer
/// bodies are the only code that stores those injected globals; groups without
/// such a store remain location-independent.
pub(crate) fn group_path_bindings(
    functions: &[brass_engine::MonoFunction<'_>],
    module_paths: &[ModulePathBinding],
) -> Vec<ModulePathBinding> {
    let globals: HashMap<_, _> = module_paths
        .iter()
        .map(|binding| {
            (
                brass_hir::qualify(MODULE_PATH_CONST, &binding.module),
                binding,
            )
        })
        .collect();
    let mut embedded: HashMap<Vec<String>, ModulePathBinding> = HashMap::new();
    for function in functions {
        for statement in function.body.blocks.iter().flat_map(|block| &block.stmts) {
            if let brass_mir::MirStmt::SetGlobal(name, _) = statement
                && let Some(binding) = globals.get(name)
            {
                embedded.insert(binding.module.clone(), (*binding).clone());
            }
        }
    }
    let mut embedded: Vec<_> = embedded.into_values().collect();
    embedded.sort_by(|left, right| left.module.cmp(&right.module));
    embedded
}

/// One object emitted during this run, paired with the exact lazy group shape
/// needed to validate and reload it later.
pub(crate) struct CapturedObject {
    pub(crate) group_key: String,
    pub(crate) symbols: Vec<String>,
    pub(crate) path_bindings: Vec<ModulePathBinding>,
    pub(crate) object: Vec<u8>,
}

/// Per-run native-cache state created by the driver after a full analysis-cache
/// hit. Construction probes the preferred compatible pack (`O2` before `O0`
/// for an `O0` run); saving always merges captures into the current tier.
pub struct ObjectCacheSession {
    entry: PathBuf,
    analysis_hash: [u8; 20],
    module_paths: CurrentModulePaths,
    objects: Option<ValidatedObjects>,
}

impl ObjectCacheSession {
    /// Load compatible native objects for `entry`, bound to `analysis_hash`.
    /// Missing, stale, mismatched, and corrupted files all produce an empty
    /// session and fall back to ordinary LLVM compilation group by group.
    pub fn load(
        entry: impl Into<PathBuf>,
        analysis_hash: [u8; 20],
        program: &brass_hir::Program,
    ) -> Self {
        let entry = entry.into();
        let module_paths = module_path_bindings(program)
            .into_iter()
            .map(|binding| (binding.module, binding.value))
            .collect();
        let objects = brass_cache::enabled()
            .then(|| load_preferred(&entry, analysis_hash, OptTier::from_env(), &module_paths))
            .flatten();
        Self {
            entry,
            analysis_hash,
            module_paths,
            objects,
        }
    }

    pub(crate) fn objects(&self) -> Option<&ValidatedObjects> {
        self.objects.as_ref()
    }

    pub(crate) fn writer(
        &self,
        group_metadata: HashMap<String, GroupMetadata>,
    ) -> Option<ObjectCacheWriter> {
        if !brass_cache::enabled() {
            return None;
        }
        ObjectCacheWriter::new(
            self.entry.clone(),
            self.analysis_hash,
            OptTier::from_env(),
            &self.module_paths,
            group_metadata,
        )
    }

    pub(crate) fn save(self, captured: Vec<CapturedObject>) {
        if brass_cache::enabled() && !captured.is_empty() {
            save_captures(
                &self.entry,
                self.analysis_hash,
                OptTier::from_env(),
                &self.module_paths,
                captured,
            );
        }
    }
}

/// Incremental publisher used by ORC while JIT code is running. Some native
/// functions terminate the process and never return to the driver, so each new
/// object is atomically merged before control enters the linked machine code.
pub(crate) struct ObjectCacheWriter {
    entry: PathBuf,
    analysis_hash: [u8; 20],
    tier: OptTier,
    target: TargetIdentity,
    group_metadata: HashMap<String, GroupMetadata>,
    groups: CachedGroups,
}

impl ObjectCacheWriter {
    fn new(
        entry: PathBuf,
        analysis_hash: [u8; 20],
        tier: OptTier,
        module_paths: &CurrentModulePaths,
        group_metadata: HashMap<String, GroupMetadata>,
    ) -> Option<Self> {
        let target = target_identity()?;
        let groups = load_tier(&entry, analysis_hash, tier, &target, module_paths)
            .map(|objects| objects.groups)
            .unwrap_or_default();
        Some(Self {
            entry,
            analysis_hash,
            tier,
            target,
            group_metadata,
            groups,
        })
    }

    pub(crate) fn record(&mut self, group_key: &str, object: &[u8]) {
        let Some(metadata) = self.group_metadata.get(group_key) else {
            return;
        };
        self.groups.insert(
            group_key.to_string(),
            CachedObject {
                symbols: metadata.symbols.clone(),
                path_bindings: metadata.path_bindings.clone(),
                object: object.to_vec(),
            },
        );
        write_groups(
            &self.entry,
            self.analysis_hash,
            self.tier,
            &self.target,
            &self.groups,
        );
    }
}

fn load_preferred(
    entry: &Path,
    analysis_hash: [u8; 20],
    tier: OptTier,
    module_paths: &CurrentModulePaths,
) -> Option<ValidatedObjects> {
    let target = target_identity()?;
    let tiers: &[OptTier] = match tier {
        OptTier::O0 => &[OptTier::O2, OptTier::O0],
        OptTier::O2 => &[OptTier::O2],
    };
    tiers
        .iter()
        .find_map(|candidate| load_tier(entry, analysis_hash, *candidate, &target, module_paths))
}

fn load_tier(
    entry: &Path,
    analysis_hash: [u8; 20],
    tier: OptTier,
    target: &TargetIdentity,
    module_paths: &CurrentModulePaths,
) -> Option<ValidatedObjects> {
    object_paths(entry, tier)
        .into_iter()
        .find_map(|path| load_path(&path, analysis_hash, tier, target, module_paths))
}

fn load_path(
    path: &Path,
    analysis_hash: [u8; 20],
    tier: OptTier,
    target: &TargetIdentity,
    module_paths: &CurrentModulePaths,
) -> Option<ValidatedObjects> {
    let bytes = std::fs::read(path).ok()?;
    let tag = brass_cache::cache_tag(&tier.cache_flavor())?;
    let body = brass_cache::decode_file(&bytes, &tag)?;
    let pack: ObjectPack = postcard::from_bytes(body).ok()?;
    let portable_generic = pack.cpu == "generic" && pack.features.is_empty();
    if pack.analysis_hash != analysis_hash
        || pack.triple != target.triple
        || (!portable_generic && (pack.cpu != target.cpu || pack.features != target.features))
    {
        return None;
    }
    let groups = pack
        .groups
        .into_iter()
        .filter_map(|group| {
            if path_bindings_match(&group.path_bindings, module_paths) {
                Some((
                    group.key,
                    CachedObject {
                        symbols: group.symbols,
                        path_bindings: group.path_bindings,
                        object: group.object,
                    },
                ))
            } else {
                tracing::debug!(
                    target: "brass::perf",
                    group = %group.key,
                    "object cache: _PATH binding mismatch"
                );
                None
            }
        })
        .collect();
    Some(ValidatedObjects { groups })
}

fn path_bindings_match(bindings: &[ModulePathBinding], current: &CurrentModulePaths) -> bool {
    bindings
        .iter()
        .all(|binding| current.get(&binding.module) == Some(&binding.value))
}

fn save_captures(
    entry: &Path,
    analysis_hash: [u8; 20],
    tier: OptTier,
    module_paths: &CurrentModulePaths,
    captured: Vec<CapturedObject>,
) {
    let group_metadata = captured
        .iter()
        .map(|capture| {
            (
                capture.group_key.clone(),
                GroupMetadata {
                    symbols: capture.symbols.clone(),
                    path_bindings: capture.path_bindings.clone(),
                },
            )
        })
        .collect();
    let Some(mut writer) = ObjectCacheWriter::new(
        entry.to_path_buf(),
        analysis_hash,
        tier,
        module_paths,
        group_metadata,
    ) else {
        return;
    };
    for capture in captured {
        writer.groups.insert(
            capture.group_key,
            CachedObject {
                symbols: capture.symbols,
                path_bindings: capture.path_bindings,
                object: capture.object,
            },
        );
    }
    write_groups(
        &writer.entry,
        writer.analysis_hash,
        writer.tier,
        &writer.target,
        &writer.groups,
    );
}

fn write_groups(
    entry: &Path,
    analysis_hash: [u8; 20],
    tier: OptTier,
    target: &TargetIdentity,
    groups: &CachedGroups,
) {
    let mut groups: Vec<_> = groups
        .iter()
        .map(|(key, cached)| PackedGroup {
            key: key.clone(),
            symbols: cached.symbols.clone(),
            path_bindings: cached.path_bindings.clone(),
            object: cached.object.clone(),
        })
        .collect();
    groups.sort_by(|left, right| left.key.cmp(&right.key));
    let pack = ObjectPack {
        analysis_hash,
        triple: target.triple.clone(),
        cpu: target.cpu.clone(),
        features: target.features.clone(),
        groups,
    };
    let (Ok(body), Some(tag)) = (
        postcard::to_stdvec(&pack),
        brass_cache::cache_tag(&tier.cache_flavor()),
    ) else {
        return;
    };
    let framed = brass_cache::encode_file(&tag, &body);
    let adjacent = adjacent_path(entry, tier);
    if brass_cache::write_atomic(&adjacent, &framed) {
        return;
    }
    let Some(fallback) = fallback_path(entry, tier) else {
        return;
    };
    let Some(directory) = fallback.parent() else {
        return;
    };
    if std::fs::create_dir_all(directory).is_ok() {
        let _ = brass_cache::write_atomic(&fallback, &framed);
    }
}

fn object_paths(entry: &Path, tier: OptTier) -> Vec<PathBuf> {
    let mut paths = vec![adjacent_path(entry, tier)];
    if let Some(fallback) = fallback_path(entry, tier) {
        paths.push(fallback);
    }
    paths
}

fn adjacent_path(entry: &Path, tier: OptTier) -> PathBuf {
    entry.with_extension(tier.extension())
}

fn fallback_path(entry: &Path, tier: OptTier) -> Option<PathBuf> {
    let identity = entry.canonicalize().unwrap_or_else(|_| entry.to_path_buf());
    let hash = brass_cache::content_hash(identity.to_string_lossy().as_bytes());
    let hex: String = hash.iter().map(|byte| format!("{byte:02x}")).collect();
    Some(brass_cache::context_dir()?.join(format!("obj-{hex}.{}", tier.extension())))
}

fn target_identity() -> Option<TargetIdentity> {
    let (cpu, features) = target_cpu_identity()?;
    // SAFETY: LLVM returns an independently allocated, NUL-terminated message
    // that is copied before being disposed exactly once below.
    unsafe {
        let triple = LLVMGetDefaultTargetTriple();
        if triple.is_null() {
            return None;
        }
        let identity = TargetIdentity {
            triple: CStr::from_ptr(triple).to_string_lossy().into_owned(),
            cpu,
            features,
        };
        LLVMDisposeMessage(triple);
        Some(identity)
    }
}

impl OptTier {
    fn extension(self) -> &'static str {
        match self {
            Self::O0 => "o0.czobj",
            Self::O2 => "o2.czobj",
        }
    }

    fn cache_flavor(self) -> String {
        let tier = match self {
            Self::O0 => "o0",
            Self::O2 => "o2",
        };
        format!("obj-v{OBJECT_PACK_FORMAT_VERSION}-{tier}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_path(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!("brass-objcache-{}-{name}", std::process::id()))
    }

    fn write_pack(path: &Path, tier: OptTier, pack: &ObjectPack) {
        let body = postcard::to_stdvec(pack).expect("encode pack");
        let tag = brass_cache::cache_tag(&tier.cache_flavor()).expect("cache tag");
        std::fs::write(path, brass_cache::encode_file(&tag, &body)).expect("write pack");
    }

    fn packed_group(key: &str, path_bindings: Vec<ModulePathBinding>) -> PackedGroup {
        PackedGroup {
            key: key.into(),
            symbols: vec![key.into()],
            path_bindings,
            object: vec![1, 2, 3],
        }
    }

    fn load_test_pack(
        path: &Path,
        analysis_hash: [u8; 20],
        tier: OptTier,
        target: &TargetIdentity,
    ) -> Option<ValidatedObjects> {
        load_path(path, analysis_hash, tier, target, &HashMap::new())
    }

    /// A damaged object body is a cache miss at the shared framing boundary,
    /// before postcard or the linker can observe any of its bytes.
    #[test]
    fn corrupted_packfile_is_ignored() {
        let path = test_path("corrupt.czobj");
        let target = target_identity().expect("native target");
        let analysis_hash = [7; 20];
        let pack = ObjectPack {
            analysis_hash,
            triple: target.triple.clone(),
            cpu: target.cpu.clone(),
            features: target.features.clone(),
            groups: vec![packed_group("foo", Vec::new())],
        };
        write_pack(&path, OptTier::O0, &pack);
        let mut bytes = std::fs::read(&path).expect("read pack");
        *bytes.last_mut().expect("nonempty pack") ^= 0xff;
        std::fs::write(&path, bytes).expect("corrupt pack");

        assert!(load_test_pack(&path, analysis_hash, OptTier::O0, &target).is_none());
        let _ = std::fs::remove_file(path);
    }

    /// Native objects require both this compiler's framed cache tag and the
    /// exact serialized analysis payload identity. Thus an object containing
    /// constants from an old wrapper AST cannot outlive that analysis cache.
    #[test]
    fn packfile_requires_compiler_and_analysis_identity() {
        let path = test_path("identity.czobj");
        let target = target_identity().expect("native target");
        let analysis_hash = [11; 20];
        let pack = ObjectPack {
            analysis_hash,
            triple: target.triple.clone(),
            cpu: target.cpu.clone(),
            features: target.features.clone(),
            groups: vec![packed_group("foo", Vec::new())],
        };
        let body = postcard::to_stdvec(&pack).expect("encode pack");
        std::fs::write(
            &path,
            brass_cache::encode_file("obsolete-compiler/obj-v2-o0", &body),
        )
        .expect("write obsolete pack");
        assert!(load_test_pack(&path, analysis_hash, OptTier::O0, &target).is_none());

        write_pack(&path, OptTier::O0, &pack);
        assert!(load_test_pack(&path, [12; 20], OptTier::O0, &target).is_none());
        let _ = std::fs::remove_file(path);
    }

    /// The object-pack version lives in the framed flavor, so postcard never
    /// attempts to decode a previous schema as the current `PackedGroup`.
    #[test]
    fn old_object_pack_version_is_ignored() {
        let path = test_path("old-version.czobj");
        let target = target_identity().expect("native target");
        let analysis_hash = [13; 20];
        let pack = ObjectPack {
            analysis_hash,
            triple: target.triple.clone(),
            cpu: target.cpu.clone(),
            features: target.features.clone(),
            groups: vec![packed_group("foo", Vec::new())],
        };
        let body = postcard::to_stdvec(&pack).expect("encode pack");
        let old_tag = brass_cache::cache_tag("obj-v1-o0").expect("old cache tag");
        std::fs::write(&path, brass_cache::encode_file(&old_tag, &body)).expect("write old pack");

        assert!(load_test_pack(&path, analysis_hash, OptTier::O0, &target).is_none());
        let _ = std::fs::remove_file(path);
    }

    /// The first symbol is only the lookup key. A changed ordered group shape
    /// must miss so codegen emits fresh IR for the entire group.
    #[test]
    fn mismatched_symbol_list_misses_group() {
        let objects = ValidatedObjects {
            groups: HashMap::from([(
                "foo".to_string(),
                CachedObject {
                    symbols: vec!["foo".to_string(), "bar".to_string()],
                    path_bindings: Vec::new(),
                    object: vec![1, 2, 3],
                },
            )]),
        };
        assert!(
            objects
                .matching_object("foo", &["foo".to_string(), "baz".to_string()])
                .is_none()
        );
    }

    /// Relocation invalidates only the group that embeds the old `_PATH`;
    /// groups with no binding remain portable within the same object pack.
    #[test]
    fn path_mismatch_drops_only_bound_group() {
        let path = test_path("path-binding.czobj");
        let target = target_identity().expect("native target");
        let analysis_hash = [17; 20];
        let module = vec!["whereami".to_string()];
        let pack = ObjectPack {
            analysis_hash,
            triple: target.triple.clone(),
            cpu: target.cpu.clone(),
            features: target.features.clone(),
            groups: vec![
                packed_group(
                    "bound",
                    vec![ModulePathBinding {
                        module: module.clone(),
                        value: "/old/whereami.cz".into(),
                    }],
                ),
                packed_group("portable", Vec::new()),
            ],
        };
        write_pack(&path, OptTier::O0, &pack);
        let current = HashMap::from([(module, "/new/whereami.cz".to_string())]);

        let objects = load_path(&path, analysis_hash, OptTier::O0, &target, &current)
            .expect("compatible pack");
        assert!(
            objects
                .matching_object("bound", &["bound".into()])
                .is_none()
        );
        assert!(
            objects
                .matching_object("portable", &["portable".into()])
                .is_some()
        );
        let _ = std::fs::remove_file(path);
    }

    /// A distribution object deliberately built for LLVM's generic CPU does
    /// not inherit the packaging machine's feature set and is reusable by a
    /// different host CPU as long as the complete target triple still matches.
    #[test]
    fn generic_pack_accepts_another_cpu_on_the_same_triple() {
        let path = test_path("generic.czobj");
        let analysis_hash = [9; 20];
        let target = TargetIdentity {
            triple: "test-unknown-linux-gnu".into(),
            cpu: "different-host".into(),
            features: "+host-extension".into(),
        };
        let pack = ObjectPack {
            analysis_hash,
            triple: target.triple.clone(),
            cpu: "generic".into(),
            features: String::new(),
            groups: vec![packed_group("foo", Vec::new())],
        };
        write_pack(&path, OptTier::O2, &pack);

        assert!(load_test_pack(&path, analysis_hash, OptTier::O2, &target).is_some());
        let _ = std::fs::remove_file(path);
    }
}
