//! Versioned native-object packfiles for lazy ORC groups.
//!
//! Each pack is bound to the serialized analysis-cache body that produced the
//! monomorphized program and to the complete native target identity. Groups
//! carry their full ordered public-symbol list as an additional structural
//! guard: a stable first-symbol key alone must never revive an object after the
//! grouping algorithm or reachable instance set changes.

use std::collections::HashMap;
use std::ffi::CStr;
use std::path::{Path, PathBuf};

use llvm_sys::core::LLVMDisposeMessage;
use llvm_sys::target_machine::LLVMGetDefaultTargetTriple;

use super::orc::{OptTier, target_cpu_identity};

type CachedGroups = HashMap<String, (Vec<String>, Vec<u8>)>;

#[derive(Clone, Debug, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
struct ObjectPack {
    analysis_hash: [u8; 20],
    triple: String,
    cpu: String,
    features: String,
    groups: Vec<(String, Vec<String>, Vec<u8>)>,
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
        let (recorded_symbols, object) = self.groups.get(key)?;
        (recorded_symbols == symbols).then_some(object.as_slice())
    }
}

/// One object emitted during this run, paired with the exact lazy group shape
/// needed to validate and reload it later.
pub(crate) struct CapturedObject {
    pub(crate) group_key: String,
    pub(crate) symbols: Vec<String>,
    pub(crate) object: Vec<u8>,
}

/// Per-run native-cache state created by the driver after a full analysis-cache
/// hit. Construction probes the preferred compatible pack (`O2` before `O0`
/// for an `O0` run); saving always merges captures into the current tier.
pub struct ObjectCacheSession {
    entry: PathBuf,
    analysis_hash: [u8; 20],
    objects: Option<ValidatedObjects>,
}

impl ObjectCacheSession {
    /// Load compatible native objects for `entry`, bound to `analysis_hash`.
    /// Missing, stale, mismatched, and corrupted files all produce an empty
    /// session and fall back to ordinary LLVM compilation group by group.
    pub fn load(entry: impl Into<PathBuf>, analysis_hash: [u8; 20]) -> Self {
        let entry = entry.into();
        let objects = brass_cache::enabled()
            .then(|| load_preferred(&entry, analysis_hash, OptTier::from_env()))
            .flatten();
        Self {
            entry,
            analysis_hash,
            objects,
        }
    }

    pub(crate) fn objects(&self) -> Option<&ValidatedObjects> {
        self.objects.as_ref()
    }

    pub(crate) fn writer(
        &self,
        group_symbols: HashMap<String, Vec<String>>,
    ) -> Option<ObjectCacheWriter> {
        if !brass_cache::enabled() {
            return None;
        }
        ObjectCacheWriter::new(
            self.entry.clone(),
            self.analysis_hash,
            OptTier::from_env(),
            group_symbols,
        )
    }

    pub(crate) fn save(self, captured: Vec<CapturedObject>) {
        if brass_cache::enabled() && !captured.is_empty() {
            save_captures(
                &self.entry,
                self.analysis_hash,
                OptTier::from_env(),
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
    group_symbols: HashMap<String, Vec<String>>,
    groups: CachedGroups,
}

impl ObjectCacheWriter {
    fn new(
        entry: PathBuf,
        analysis_hash: [u8; 20],
        tier: OptTier,
        group_symbols: HashMap<String, Vec<String>>,
    ) -> Option<Self> {
        let target = target_identity()?;
        let groups = load_tier(&entry, analysis_hash, tier, &target)
            .map(|objects| objects.groups)
            .unwrap_or_default();
        Some(Self {
            entry,
            analysis_hash,
            tier,
            target,
            group_symbols,
            groups,
        })
    }

    pub(crate) fn record(&mut self, group_key: &str, object: &[u8]) {
        let Some(symbols) = self.group_symbols.get(group_key).cloned() else {
            return;
        };
        self.groups
            .insert(group_key.to_string(), (symbols, object.to_vec()));
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
) -> Option<ValidatedObjects> {
    let target = target_identity()?;
    let tiers: &[OptTier] = match tier {
        OptTier::O0 => &[OptTier::O2, OptTier::O0],
        OptTier::O2 => &[OptTier::O2],
    };
    tiers
        .iter()
        .find_map(|candidate| load_tier(entry, analysis_hash, *candidate, &target))
}

fn load_tier(
    entry: &Path,
    analysis_hash: [u8; 20],
    tier: OptTier,
    target: &TargetIdentity,
) -> Option<ValidatedObjects> {
    object_paths(entry, tier)
        .into_iter()
        .find_map(|path| load_path(&path, analysis_hash, tier, target))
}

fn load_path(
    path: &Path,
    analysis_hash: [u8; 20],
    tier: OptTier,
    target: &TargetIdentity,
) -> Option<ValidatedObjects> {
    let bytes = std::fs::read(path).ok()?;
    let tag = brass_cache::cache_tag(tier.cache_flavor())?;
    let body = brass_cache::decode_file(&bytes, &tag)?;
    let pack: ObjectPack = postcard::from_bytes(body).ok()?;
    let portable_generic = pack.cpu == "generic" && pack.features.is_empty();
    if pack.analysis_hash != analysis_hash
        || pack.triple != target.triple
        || (!portable_generic && (pack.cpu != target.cpu || pack.features != target.features))
    {
        return None;
    }
    Some(ValidatedObjects {
        groups: pack
            .groups
            .into_iter()
            .map(|(key, symbols, object)| (key, (symbols, object)))
            .collect(),
    })
}

fn save_captures(
    entry: &Path,
    analysis_hash: [u8; 20],
    tier: OptTier,
    captured: Vec<CapturedObject>,
) {
    let group_symbols = captured
        .iter()
        .map(|capture| (capture.group_key.clone(), capture.symbols.clone()))
        .collect();
    let Some(mut writer) =
        ObjectCacheWriter::new(entry.to_path_buf(), analysis_hash, tier, group_symbols)
    else {
        return;
    };
    for capture in captured {
        writer
            .groups
            .insert(capture.group_key, (capture.symbols, capture.object));
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
        .map(|(key, (symbols, object))| (key.clone(), symbols.clone(), object.clone()))
        .collect();
    groups.sort_by(|left, right| left.0.cmp(&right.0));
    let pack = ObjectPack {
        analysis_hash,
        triple: target.triple.clone(),
        cpu: target.cpu.clone(),
        features: target.features.clone(),
        groups,
    };
    let (Ok(body), Some(tag)) = (
        postcard::to_stdvec(&pack),
        brass_cache::cache_tag(tier.cache_flavor()),
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

    fn cache_flavor(self) -> &'static str {
        match self {
            Self::O0 => "obj-o0",
            Self::O2 => "obj-o2",
        }
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
        let tag = brass_cache::cache_tag(tier.cache_flavor()).expect("cache tag");
        std::fs::write(path, brass_cache::encode_file(&tag, &body)).expect("write pack");
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
            groups: vec![("foo".into(), vec!["foo".into()], vec![1, 2, 3])],
        };
        write_pack(&path, OptTier::O0, &pack);
        let mut bytes = std::fs::read(&path).expect("read pack");
        *bytes.last_mut().expect("nonempty pack") ^= 0xff;
        std::fs::write(&path, bytes).expect("corrupt pack");

        assert!(load_path(&path, analysis_hash, OptTier::O0, &target).is_none());
        let _ = std::fs::remove_file(path);
    }

    /// The first symbol is only the lookup key. A changed ordered group shape
    /// must miss so codegen emits fresh IR for the entire group.
    #[test]
    fn mismatched_symbol_list_misses_group() {
        let objects = ValidatedObjects {
            groups: HashMap::from([(
                "foo".to_string(),
                (vec!["foo".to_string(), "bar".to_string()], vec![1, 2, 3]),
            )]),
        };
        assert!(
            objects
                .matching_object("foo", &["foo".to_string(), "baz".to_string()])
                .is_none()
        );
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
            groups: vec![("foo".into(), vec!["foo".into()], vec![1, 2, 3])],
        };
        write_pack(&path, OptTier::O2, &pack);

        assert!(load_path(&path, analysis_hash, OptTier::O2, &target).is_some());
        let _ = std::fs::remove_file(path);
    }
}
