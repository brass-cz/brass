//! Content-addressed native objects for ORC sessions. Keys describe the exact
//! input to optimization and instruction selection; storage never depends on
//! source paths, analysis artifacts, or a separately maintained symbol list.

use std::ffi::OsString;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};
use std::time::{SystemTime, UNIX_EPOCH};

use sha2::{Digest, Sha256};

use super::orc::OptTier;

const MAGIC: &[u8; 8] = b"CZOBJ\0\0\0";
const FORMAT_VERSION: u32 = 1;
const HEADER_LEN: usize = 8 + 4 + 8 + 32;
const DEFAULT_MAX_MB: u64 = 256;
static STORE: OnceLock<Option<Arc<ObjectStore>>> = OnceLock::new();
static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

/// Disable the process object store before any session is constructed. Integration
/// test binaries call this before creating backends, protecting the user's cache.
/// Repeated calls are allowed only when storage was already pinned off.
#[doc(hidden)]
pub fn disable_jit_cache_for_tests() {
    assert!(
        STORE.get_or_init(|| None).is_none(),
        "JIT store already enabled"
    );
}

/// The target settings passed to LLJIT, retained with the session so a key
/// describes the same machine that performs instruction selection.
pub(super) struct TargetIdentity {
    pub(super) triple: String,
    pub(super) cpu: String,
    pub(super) features: String,
}

/// Shared best-effort storage. Published files are immutable except for their
/// access timestamps. The eviction flag belongs to the process-wide store,
/// rather than to a session, to bound directory scans across multiple sessions.
pub(crate) struct ObjectStore {
    directory: PathBuf,
    tag: String,
    max_bytes: u64,
    evicted: AtomicBool,
}

impl ObjectStore {
    /// Samples configuration and compiler identity once for the entire process.
    /// Disabled or unidentifiable builds never create a cache directory.
    pub(crate) fn from_env() -> Option<Arc<Self>> {
        // Unit tests must explicitly inject their store; library tests also
        // construct sessions through higher-level compiler entry points.
        if cfg!(test) {
            return None;
        }
        STORE
            .get_or_init(|| {
                Self::configured(|name| std::env::var_os(name), compiler_identity()).map(Arc::new)
            })
            .clone()
    }

    fn configured(get: impl Fn(&str) -> Option<OsString>, tag: Option<String>) -> Option<Self> {
        if matches!(
            get("BRASS_JIT_CACHE").as_deref().and_then(|s| s.to_str()),
            Some("off" | "0")
        ) {
            return None;
        }
        let directory = get("XDG_CACHE_HOME")
            .filter(|path| !path.is_empty())
            .map(PathBuf::from)
            .or_else(|| {
                get("HOME")
                    .filter(|path| !path.is_empty())
                    .map(|home| PathBuf::from(home).join(".cache"))
            })?
            .join("brass/jit");
        let max_mb = get("BRASS_JIT_CACHE_MAX_MB")
            .and_then(|value| value.to_str()?.parse::<u64>().ok())
            .unwrap_or(DEFAULT_MAX_MB);
        Some(Self {
            directory,
            tag: tag?,
            max_bytes: max_mb.saturating_mul(1024 * 1024),
            evicted: AtomicBool::new(false),
        })
    }

    /// Hashes unoptimized bitcode after its final data layout has been set.
    /// Length prefixes make field boundaries unambiguous even for arbitrary
    /// LLVM strings. The tier is explicit so an O0 session can prefer O2.
    pub(super) fn key(&self, target: &TargetIdentity, tier: OptTier, bitcode: &[u8]) -> String {
        let mut hash = Sha256::new();
        hash.update(FORMAT_VERSION.to_le_bytes());
        for field in [
            self.tag.as_bytes(),
            target.triple.as_bytes(),
            target.cpu.as_bytes(),
            target.features.as_bytes(),
        ] {
            hash.update((field.len() as u64).to_le_bytes());
            hash.update(field);
        }
        hash.update([match tier {
            OptTier::O0 => 0,
            OptTier::O2 => 2,
        }]);
        hash.update(bitcode);
        hash.finalize()
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect()
    }

    /// Returns only fully validated objects and refreshes their recency. Keys
    /// must come from `key`; rejected files are removed so the next compilation
    /// can repair them. I/O failure always behaves like an ordinary miss.
    pub(super) fn load(&self, key: &str, symbol: &str) -> Option<Vec<u8>> {
        let path = self.directory.join(format!("{key}.czobj"));
        let bytes = match fs::read(&path) {
            Ok(bytes) => bytes,
            Err(error) => {
                if error.kind() != io::ErrorKind::NotFound {
                    log_io("read", &path, &error);
                }
                return None;
            }
        };
        let Some(payload) = decode(&bytes) else {
            tracing::debug!(target: "brass::perf", key, "jit cache invalid object");
            remove(&path);
            return None;
        };
        if let Err(error) = File::open(&path).and_then(|file| file.set_modified(SystemTime::now()))
        {
            log_io("touch", &path, &error);
        }
        tracing::debug!(target: "brass::perf", symbol, key, "jit cache hit");
        Some(payload.to_vec())
    }

    /// Publishes during the object transform, before JIT execution can exit the
    /// process. A same-directory rename makes every visible object complete;
    /// concurrent writers for the same content key are interchangeable.
    pub(super) fn publish(&self, key: &str, symbol: &str, payload: &[u8]) {
        let path = self.directory.join(format!("{key}.czobj"));
        if let Err(error) = fs::create_dir_all(&self.directory) {
            log_io("mkdir", &self.directory, &error);
            return;
        }
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos();
        let sequence = TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let temp = self.directory.join(format!(
            ".{key}-{}-{nonce}-{sequence}.tmp",
            std::process::id()
        ));
        let result = (|| -> io::Result<()> {
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&temp)?;
            file.write_all(MAGIC)?;
            file.write_all(&FORMAT_VERSION.to_le_bytes())?;
            file.write_all(&(payload.len() as u64).to_le_bytes())?;
            file.write_all(&Sha256::digest(payload))?;
            file.write_all(payload)?;
            drop(file);
            fs::rename(&temp, &path)
        })();
        if let Err(error) = result {
            log_io("publish", &path, &error);
            remove(&temp);
            return;
        }
        tracing::debug!(target: "brass::perf", symbol, key, "jit cache store");
        if !self.evicted.swap(true, Ordering::Relaxed) {
            self.evict();
        }
    }

    fn evict(&self) {
        let entries = match fs::read_dir(&self.directory) {
            Ok(entries) => entries,
            Err(error) => {
                log_io("scan", &self.directory, &error);
                return;
            }
        };
        let mut files = Vec::new();
        let mut total = 0u64;
        for entry in entries {
            let entry = match entry {
                Ok(entry) => entry,
                Err(error) => {
                    log_io("scan entry", &self.directory, &error);
                    continue;
                }
            };
            let path = entry.path();
            if path.extension().is_none_or(|ext| ext != "czobj") {
                continue;
            }
            match entry
                .metadata()
                .and_then(|metadata| Ok((metadata.len(), metadata.modified()?, metadata.is_file())))
            {
                Ok((size, modified, true)) => {
                    total = total.saturating_add(size);
                    files.push((modified, path, size));
                }
                Ok(_) => {}
                Err(error) => log_io("stat", &path, &error),
            }
        }
        if total <= self.max_bytes {
            return;
        }
        files.sort_by_key(|(modified, _, _)| *modified);
        let target = (u128::from(self.max_bytes) * 80 / 100) as u64;
        for (_, path, size) in files {
            if total <= target {
                break;
            }
            match fs::remove_file(&path) {
                Ok(()) => total = total.saturating_sub(size),
                Err(error) if error.kind() == io::ErrorKind::NotFound => {
                    total = total.saturating_sub(size)
                }
                Err(error) => log_io("evict", &path, &error),
            }
        }
    }

    /// Injects storage and identity without changing the process environment.
    #[cfg(test)]
    pub(super) fn isolated(directory: PathBuf, max_bytes: u64) -> Arc<Self> {
        Arc::new(Self {
            directory,
            tag: "test-compiler".into(),
            max_bytes,
            evicted: AtomicBool::new(false),
        })
    }
}

fn compiler_identity() -> Option<String> {
    let tag = brass_metadata::compiler_tag();
    if brass_metadata::build_channel() != brass_metadata::BuildChannel::Nightly {
        return Some(tag);
    }
    let fingerprint = (|| -> io::Result<_> {
        let metadata = fs::metadata(std::env::current_exe()?)?;
        let modified = metadata
            .modified()?
            .duration_since(UNIX_EPOCH)
            .map_err(io::Error::other)?;
        Ok(format!("{tag}/{}-{}", modified.as_nanos(), metadata.len()))
    })();
    match fingerprint {
        Ok(tag) => Some(tag),
        Err(error) => {
            tracing::debug!(target: "brass::perf", %error, "jit cache disabled: executable identity unavailable");
            None
        }
    }
}

fn decode(bytes: &[u8]) -> Option<&[u8]> {
    if bytes.len() < HEADER_LEN
        || &bytes[..8] != MAGIC
        || bytes[8..12] != FORMAT_VERSION.to_le_bytes()
    {
        return None;
    }
    let length = u64::from_le_bytes(bytes[12..20].try_into().ok()?);
    let payload = &bytes[HEADER_LEN..];
    if length != payload.len() as u64 || bytes[20..HEADER_LEN] != Sha256::digest(payload)[..] {
        return None;
    }
    Some(payload)
}

fn log_io(operation: &str, path: &Path, error: &io::Error) {
    tracing::debug!(target: "brass::perf", operation, path = %path.display(), %error, "jit cache I/O failure");
}

fn remove(path: &Path) {
    if let Err(error) = fs::remove_file(path)
        && error.kind() != io::ErrorKind::NotFound
    {
        log_io("remove", path, &error);
    }
}

/// Removes isolated test storage even when an assertion unwinds.
#[cfg(test)]
pub(super) struct TestDirectory(pub(super) PathBuf);

#[cfg(test)]
impl TestDirectory {
    pub(super) fn new() -> Self {
        let sequence = TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        Self(std::env::temp_dir().join(format!(
            "brass-objcache-{}-{nonce}-{sequence}",
            std::process::id()
        )))
    }
}

#[cfg(test)]
impl Drop for TestDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn target() -> TargetIdentity {
        TargetIdentity {
            triple: "test-triple".into(),
            cpu: "test-cpu".into(),
            features: "+test".into(),
        }
    }

    /// Every compiler input affects the key, with unambiguous string boundaries.
    #[test]
    fn key_tracks_all_compiler_inputs() {
        let directory = TestDirectory::new();
        let mut store = ObjectStore::isolated(directory.0.clone(), u64::MAX);
        let base = store.key(&target(), OptTier::O0, b"bitcode");
        assert_eq!(base.len(), 64);
        assert!(base.bytes().all(|byte| byte.is_ascii_hexdigit()));
        assert_eq!(base, store.key(&target(), OptTier::O0, b"bitcode"));
        assert_ne!(base, store.key(&target(), OptTier::O0, b"changed"));
        assert_ne!(base, store.key(&target(), OptTier::O2, b"bitcode"));
        for field in 0..3 {
            let mut changed = target();
            match field {
                0 => changed.triple.push('x'),
                1 => changed.cpu.push('x'),
                _ => changed.features.push('x'),
            }
            assert_ne!(base, store.key(&changed, OptTier::O0, b"bitcode"));
        }
        Arc::get_mut(&mut store).unwrap().tag.push('x');
        assert_ne!(base, store.key(&target(), OptTier::O0, b"bitcode"));
        let a = TargetIdentity {
            triple: "ab".into(),
            cpu: "c".into(),
            features: String::new(),
        };
        let b = TargetIdentity {
            triple: "a".into(),
            cpu: "bc".into(),
            features: String::new(),
        };
        assert_ne!(
            store.key(&a, OptTier::O0, b""),
            store.key(&b, OptTier::O0, b"")
        );
    }

    /// Framing rejects each damaged field, truncation, and trailing data,
    /// deletes the rejected entry, and permits immediate replacement.
    #[test]
    fn invalid_objects_are_deleted_and_replaceable() {
        let directory = TestDirectory::new();
        let store = ObjectStore::isolated(directory.0.clone(), u64::MAX);
        let key = store.key(&target(), OptTier::O0, b"ir");
        let path = directory.0.join(format!("{key}.czobj"));
        store.publish(&key, "test", b"native object");
        let good = fs::read(&path).unwrap();
        let mut invalid = Vec::new();
        for index in [0, 8, 12, 20, HEADER_LEN] {
            let mut bytes = good.clone();
            bytes[index] ^= 1;
            invalid.push(bytes);
        }
        invalid.push(good[..HEADER_LEN - 1].to_vec());
        invalid.push(good[..good.len() - 1].to_vec());
        invalid.push([good.as_slice(), b"x"].concat());
        for bytes in invalid {
            fs::write(&path, bytes).unwrap();
            assert!(store.load(&key, "test").is_none());
            assert!(!path.exists());
            store.publish(&key, "test", b"native object");
            assert_eq!(store.load(&key, "test").unwrap(), b"native object");
        }
    }

    /// Configuration is injectable: both opt-outs, missing directories, and
    /// unavailable build identity leave the filesystem untouched.
    #[test]
    fn disabled_configuration_never_opens_storage() {
        let directory = TestDirectory::new();
        for disabled in ["off", "0"] {
            let store = ObjectStore::configured(
                |name| match name {
                    "BRASS_JIT_CACHE" => Some(disabled.into()),
                    "XDG_CACHE_HOME" => Some(directory.0.as_os_str().to_owned()),
                    _ => None,
                },
                Some("tag".into()),
            );
            assert!(store.is_none());
        }
        assert!(ObjectStore::configured(|_| None, Some("tag".into())).is_none());
        assert!(ObjectStore::configured(|_| Some(OsString::new()), Some("tag".into())).is_none());
        assert!(
            ObjectStore::configured(|_| Some(directory.0.as_os_str().to_owned()), None).is_none()
        );
        assert!(!directory.0.exists());
    }

    /// XDG takes precedence, HOME supplies the fallback, and caps are in MiB.
    #[test]
    fn directory_and_cap_configuration() {
        let directory = TestDirectory::new();
        let settings = |name: &str| match name {
            "HOME" => Some(directory.0.as_os_str().to_owned()),
            "BRASS_JIT_CACHE_MAX_MB" => Some("2".into()),
            _ => None,
        };
        let fallback = ObjectStore::configured(settings, Some("tag".into())).unwrap();
        assert_eq!(fallback.directory, directory.0.join(".cache/brass/jit"));
        assert_eq!(fallback.max_bytes, 2 * 1024 * 1024);
        let xdg = ObjectStore::configured(
            |name| {
                if name == "XDG_CACHE_HOME" {
                    Some(directory.0.join("xdg").into_os_string())
                } else {
                    settings(name)
                }
            },
            Some("tag".into()),
        )
        .unwrap();
        assert_eq!(xdg.directory, directory.0.join("xdg/brass/jit"));
        assert!(!directory.0.exists());
    }

    /// Hits protect old entries by refreshing mtime; eviction crosses the
    /// 80-percent watermark once, and ignores unrelated directory contents.
    #[test]
    fn eviction_respects_recency_and_runs_once() {
        let directory = TestDirectory::new();
        let seed = ObjectStore::isolated(directory.0.clone(), u64::MAX);
        let keys: Vec<_> = (0..5)
            .map(|n| seed.key(&target(), OptTier::O0, &[n]))
            .collect();
        let path = |n: usize| directory.0.join(format!("{}.czobj", keys[n]));
        for (index, key) in keys[..3].iter().enumerate() {
            seed.publish(key, "test", &[0; 100]);
            File::open(path(index))
                .unwrap()
                .set_modified(UNIX_EPOCH + std::time::Duration::from_secs(index as u64))
                .unwrap();
        }
        fs::write(directory.0.join("unrelated.tmp"), [0; 1000]).unwrap();
        assert!(seed.load(&keys[0], "test").is_some());
        assert!(
            fs::metadata(path(0)).unwrap().modified().unwrap()
                > UNIX_EPOCH + std::time::Duration::from_secs(2)
        );
        let bounded = ObjectStore::isolated(directory.0.clone(), 500);
        bounded.publish(&keys[3], "test", &[0; 100]);
        assert!(path(0).exists());
        assert!(!path(1).exists());
        assert!(!path(2).exists());
        assert!(path(3).exists());
        assert!(directory.0.join("unrelated.tmp").exists());
        bounded.publish(&keys[4], "test", &[0; 600]);
        assert!(path(0).exists(), "only the first publish evicts");
    }

    /// Concurrent publications expose a complete frame and leave no temp files.
    #[test]
    fn concurrent_writers_publish_complete_objects() {
        let directory = TestDirectory::new();
        let store = ObjectStore::isolated(directory.0.clone(), u64::MAX);
        let key = store.key(&target(), OptTier::O0, b"ir");
        std::thread::scope(|scope| {
            for _ in 0..8 {
                scope.spawn(|| store.publish(&key, "test", &[42; 4096]));
            }
        });
        assert_eq!(store.load(&key, "test").unwrap(), [42; 4096]);
        assert_eq!(fs::read_dir(&directory.0).unwrap().count(), 1);
    }

    /// Unusable storage never turns cache operations into compiler errors.
    #[test]
    fn io_failures_are_misses() {
        let directory = TestDirectory::new();
        fs::create_dir_all(&directory.0).unwrap();
        let file = directory.0.join("file");
        fs::write(&file, b"not a directory").unwrap();
        let store = ObjectStore::isolated(file, u64::MAX);
        let key = store.key(&target(), OptTier::O0, b"ir");
        store.publish(&key, "test", b"object");
        assert!(store.load(&key, "test").is_none());
    }
}
