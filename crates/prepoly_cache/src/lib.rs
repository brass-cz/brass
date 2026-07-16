//! The on-disk analysis cache (`.ppcache`), shared by the `prepoly` driver and
//! the `ppls` language server.
//!
//! Type checking dominates start-up time (hundreds of milliseconds on a
//! library-heavy program; parsing and lowering are single-digit), so the cache
//! stores what the checker computed rather than anything the cheap phases
//! produce: the FINAL module ASTs -- after import canonicalization, qualified-use
//! resolution, spawn auto-acquire, and reflective (`-> infer!`) specialization,
//! so a keyed program's second full pass is skipped too -- plus the analysis
//! channels the back ends consume (`expr_types` and friends). On a hit the
//! driver re-lowers the cached ASTs (deterministic, a few milliseconds) and goes
//! straight to MIR; MIR itself is NOT cached, because lowering it takes ~2ms and
//! caching it would not remove the HIR rebuild the back ends need anyway.
//!
//! A cache is written next to its entry file (`app.pp` -> `app.ppcache`), only
//! after an analysis with NO diagnostics, and names every source file that went
//! into the build. It is reused only when every one of those files still has
//! the same contents (length and SHA-1 -- see `FileStamp`) and the compiler tag
//! matches. Sources are named RELATIVE to the root each was resolved under
//! (the entry file's directory, an include root, a package root), never by
//! machine path -- so a cache survives the whole project moving, and one packed
//! alongside a release's `bin/` and `libraries/` validates wherever they are
//! installed. The resolution environment is not part of the key either: if
//! `PREPOLY_PACKAGES` or `PREPOLY_INCLUDE` change WHERE a name resolves, the
//! resolved file's contents decide -- equal bytes are the same program, and
//! different bytes miss. Any mismatch, short read, or decode error falls back
//! to the full pipeline -- the cache can never make a build wrong, only
//! faster.
//!
//! The format is binary (postcard: varint-packed serde, no field names), chosen
//! for load speed and size; it is not meant to be read by humans, and no
//! compatibility across compiler versions is attempted -- the header pins both
//! the format and the compiler version, and anything else is discarded.

use std::path::{Path, PathBuf};

use prepoly_hir::{LoadedModule, Type};
use prepoly_metadata::{BuildChannel, compiler_tag};
use prepoly_parser::Span;

/// Bumped whenever the payload layout changes, so an old file is discarded by
/// the header check instead of misread by postcard (which carries no schema).
pub const FORMAT_VERSION: u16 = 2;

/// Leading magic, so a foreign file is rejected before any decoding.
const MAGIC: &[u8; 8] = b"PPCACHE\0";

/// Where a source file was resolved from, recorded WITHOUT the machine path so
/// the stamp can be re-anchored on another machine or after the project moves.
/// Relative components are stored `/`-joined, so a cache written on one
/// platform reads on another.
#[derive(Debug, serde::Serialize, serde::Deserialize)]
pub enum StampOrigin {
    /// Relative to the entry file's directory (the project's own sources).
    Entry(String),
    /// Relative to SOME include root; validation walks the current include
    /// roots in resolution order (`PREPOLY_INCLUDE`, then the distribution's
    /// implicit `<bin>/../libraries`) and judges the first candidate that
    /// exists -- exactly the shadowing the loader itself would apply.
    Include(String),
    /// Relative to the named `PREPOLY_PACKAGES` package's root.
    Package(String, String),
    /// Outside every known root; only its absolute path can find it again.
    /// Such a cache still works in place, it just cannot be relocated.
    Absolute(String),
}

/// One source file the cached build read, identified by ORIGIN plus CONTENTS: a
/// changed length or SHA-1 invalidates the cache. The embedded standard library
/// has no file and is covered by the compiler tag instead.
///
/// Content, not modification time, because a stamp has to survive the file being
/// copied. A cache shipped with a release is unpacked from an archive, which
/// restores whatever mtime it likes -- at whole-second precision, in the tar
/// format the release uses -- so an mtime key would reject a distributed cache
/// on every machine. Content also makes the stamp exact rather than merely
/// conservative: rewriting a file with the same bytes (a checkout, a formatter
/// that changed nothing) no longer forces a re-check. And content is what makes
/// the ORIGIN sound: whichever file a root resolves the reference to, equal
/// bytes mean the identical program, so no path needs to be part of the key.
#[derive(serde::Serialize, serde::Deserialize)]
pub struct FileStamp {
    pub origin: StampOrigin,
    pub len: u64,
    pub sha1: [u8; 20],
}

/// The roots stamps are recorded against and re-anchored from.
pub struct StampRoots<'a> {
    /// The entry file's directory (canonicalized).
    pub entry_dir: PathBuf,
    pub search: &'a prepoly_resolve::SearchPaths,
}

impl<'a> StampRoots<'a> {
    pub fn new(entry: &Path, search: &'a prepoly_resolve::SearchPaths) -> StampRoots<'a> {
        let dir = entry.parent().unwrap_or(Path::new("."));
        StampRoots {
            entry_dir: dir.canonicalize().unwrap_or_else(|_| dir.to_path_buf()),
            search,
        }
    }
}

impl FileStamp {
    /// Stamp `path` as it currently exists, classifying it against `roots` --
    /// the entry directory first (a project's own files), then the package and
    /// include roots. `None` when the file cannot be read.
    pub fn of(path: &Path, roots: &StampRoots) -> Option<FileStamp> {
        let bytes = std::fs::read(path).ok()?;
        let canon = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
        let rel_under = |root: &Path| -> Option<String> {
            let root = root.canonicalize().ok()?;
            let rel = canon.strip_prefix(&root).ok()?;
            let parts: Vec<String> = rel
                .components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect();
            Some(parts.join("/"))
        };
        let origin = if let Some(rel) = rel_under(&roots.entry_dir) {
            StampOrigin::Entry(rel)
        } else if let Some((name, rel)) = roots
            .search
            .packages
            .iter()
            .find_map(|(name, root)| Some((name.clone(), rel_under(root)?)))
        {
            StampOrigin::Package(name, rel)
        } else if let Some(rel) = roots
            .search
            .includes
            .iter()
            .find_map(|root| rel_under(root))
        {
            StampOrigin::Include(rel)
        } else {
            StampOrigin::Absolute(canon.display().to_string())
        };
        Some(FileStamp {
            origin,
            len: bytes.len() as u64,
            sha1: sha1(&bytes),
        })
    }

    /// Re-anchor this stamp under the CURRENT roots and check the file it finds.
    ///
    /// The candidate is the first file the current roots produce for the
    /// recorded reference, in the loader's own precedence -- so a file that now
    /// SHADOWS the recorded one is the one judged, and a shadow with different
    /// contents misses rather than silently reviving the recorded file's
    /// analysis. The length is checked from the directory entry first, so a
    /// file that obviously differs is rejected without reading it.
    fn still_valid(&self, roots: &StampRoots) -> bool {
        let Some(candidate) = self.candidate(roots) else {
            return false;
        };
        if !std::fs::metadata(&candidate).is_ok_and(|meta| meta.len() == self.len) {
            return false;
        }
        std::fs::read(&candidate).is_ok_and(|bytes| sha1(&bytes) == self.sha1)
    }

    /// The file the recorded origin resolves to under the current roots.
    fn candidate(&self, roots: &StampRoots) -> Option<PathBuf> {
        let join = |root: &Path, rel: &str| {
            let mut p = root.to_path_buf();
            for part in rel.split('/') {
                p.push(part);
            }
            p
        };
        match &self.origin {
            StampOrigin::Entry(rel) => Some(join(&roots.entry_dir, rel)),
            StampOrigin::Package(name, rel) => Some(join(roots.search.packages.get(name)?, rel)),
            StampOrigin::Include(rel) => {
                // A project file with the same relative path shadows an include
                // (imports resolve relative to the importing file first), so it
                // is the candidate when it exists.
                let local = join(&roots.entry_dir, rel);
                if local.is_file() {
                    return Some(local);
                }
                roots
                    .search
                    .includes
                    .iter()
                    .map(|root| join(root, rel))
                    .find(|p| p.is_file())
            }
            StampOrigin::Absolute(path) => Some(PathBuf::from(path)),
        }
    }
}

fn sha1(bytes: &[u8]) -> [u8; 20] {
    use sha1::{Digest, Sha1};

    let mut out = [0u8; 20];
    out.copy_from_slice(&Sha1::digest(bytes));
    out
}

/// The checker outputs the rest of the pipeline consumes, keyed by source span.
/// Spans reproduce exactly on a hit because the cached ASTs carry them and
/// lowering never reassigns one.
#[derive(Default, serde::Serialize, serde::Deserialize)]
pub struct Channels {
    pub expr_types: Vec<(Span, Type)>,
    pub view_args: Vec<Span>,
    // No serde default: an old cache missing this field must fail to load (a
    // full recheck) rather than silently drop the coercions it encodes.
    pub sum_views: Vec<(Span, Type)>,
    pub call_locations: Vec<(Span, (String, u32, u32))>,
    pub lift_errs: Vec<Span>,
    pub fields_loops: Vec<(Span, Vec<String>)>,
    pub type_names: Vec<(Span, String)>,
    pub typeof_types: Vec<(Span, Type)>,
    pub null_props: Vec<Span>,
}

/// Everything a `.ppcache` stores.
#[derive(serde::Serialize, serde::Deserialize)]
pub struct Payload {
    /// Every on-disk source the build read, entry file included.
    pub deps: Vec<FileStamp>,
    /// The final module graph: post-resolution, post-rewrite, post-keyed
    /// specialization. Re-lowering these reproduces the checked program.
    pub modules: Vec<LoadedModule>,
    pub channels: Channels,
}

/// The cache path for an entry file: `app.pp` -> `app.ppcache`, next to it.
/// An extensionless entry (a `#!` script such as `ppm`) gains the extension.
pub fn cache_path(entry: &Path) -> PathBuf {
    entry.with_extension("ppcache")
}

/// The tag written into the header: the compiler's identity
/// ([`prepoly_metadata::compiler_tag`] -- version, channel, commit) and the
/// payload format version, plus -- for a working-tree build ONLY -- the running
/// executable's modification time.
///
/// A released compiler (a channel the release workflow stamped) is fully
/// identified by its channel and commit, so its tag is the same on every machine
/// that installs that release: a `.ppcache` written when the libraries are
/// packed carries a tag the installed compiler reproduces, which is what lets a
/// cache ship alongside them. An executable mtime differs per install and would
/// reject every distributed cache, so it is left out there.
///
/// `nightly` is the channel of a build with no release stamp, i.e. one built
/// from a working tree, and such a build is NOT identified by its commit -- the
/// source changes while the commit does not. A cache written by an earlier build
/// of the same commit must not survive the recompile, and the executable's mtime
/// is what rules it out. The mtime, rather than the executable's contents,
/// because it must be read on every cache hit and the compiler is tens of
/// megabytes; a local rebuild always moves it.
fn cache_tag() -> String {
    let tag = format!("{}/{}", compiler_tag(), FORMAT_VERSION);
    if prepoly_metadata::build_channel() != BuildChannel::Nightly {
        return tag;
    }
    format!("{tag}/{}", exe_mtime_nanos().unwrap_or(0))
}

fn exe_mtime_nanos() -> Option<u128> {
    let exe = std::env::current_exe().ok()?;
    let mtime = std::fs::metadata(exe).ok()?.modified().ok()?;
    Some(mtime.duration_since(std::time::UNIX_EPOCH).ok()?.as_nanos())
}

/// Whether caching is enabled at all (`PREPOLY_CACHE=off`/`0` disables it,
/// for debugging and for tests that must exercise the full pipeline).
pub fn enabled() -> bool {
    !matches!(
        std::env::var("PREPOLY_CACHE").as_deref(),
        Ok("off") | Ok("0")
    )
}

/// Load and validate the cache for `entry` under the current resolution roots.
/// `None` -- silently, the caller falls back to the full pipeline -- when the
/// file is missing, foreign, from another compiler version or format, or any
/// recorded source reference now resolves to different contents.
pub fn load(entry: &Path, search: &prepoly_resolve::SearchPaths) -> Option<Payload> {
    let roots = StampRoots::new(entry, search);
    let path = cache_path(entry);
    let bytes = std::fs::read(&path).ok()?;
    let rest = bytes.strip_prefix(MAGIC.as_slice())?;
    let (tag, body) = {
        let n = *rest.first()? as usize;
        let tag = std::str::from_utf8(rest.get(1..1 + n)?).ok()?;
        (tag, rest.get(1 + n..)?)
    };
    if tag != cache_tag() {
        tracing::debug!(target: "prepoly::perf", "cache: compiler tag mismatch, ignoring {}", path.display());
        return None;
    }
    let payload: Payload = postcard::from_bytes(body).ok()?;
    for dep in &payload.deps {
        if !dep.still_valid(&roots) {
            tracing::debug!(target: "prepoly::perf", "cache: {:?} changed, ignoring {}", dep.origin, path.display());
            return None;
        }
    }
    Some(payload)
}

/// Write the cache for `entry`, best-effort: a read-only directory or any
/// other write failure is ignored -- the cache is an accelerator, never a
/// requirement. The write goes through a temporary file and a rename, so a
/// concurrent reader never sees a torn cache.
pub fn save(entry: &Path, payload: &Payload) {
    let Ok(body) = postcard::to_stdvec(payload) else {
        return;
    };
    let tag = cache_tag();
    let mut bytes = Vec::with_capacity(MAGIC.len() + 1 + tag.len() + body.len());
    bytes.extend_from_slice(MAGIC);
    bytes.push(tag.len() as u8);
    bytes.extend_from_slice(tag.as_bytes());
    bytes.extend_from_slice(&body);
    let path = cache_path(entry);
    let tmp = path.with_extension("ppcache.tmp");
    if std::fs::write(&tmp, &bytes).is_ok() {
        let _ = std::fs::rename(&tmp, &path);
    }
}

// ===== the context seed cache (`.ppctx`) =====

/// The key of a context (every module of a program except its entry): the
/// compiler tag hashed together with the modules' full serialized form --
/// module paths, ASTs, spans -- so any change of content, name, or order is a
/// different context. Content-addressed, so no further validation is needed
/// beyond the tag echo inside the file.
/// The key of a context (every module of a program except its entry): the
/// compiler tag, the module names in load order, and the SHA-1 of every source
/// text that is not the entry's -- so any change of content, name, or order is
/// a different context, while the entry changing (which shifts every later
/// span) is not. `flavor` distinguishes front ends whose rewrite passes differ
/// (the driver auto-acquires `spawn` bodies; the language server does not), so
/// each seeds its own entry rather than consuming tables built over different
/// ASTs.
pub fn context_key(
    flavor: &str,
    module_names: impl Iterator<Item = String>,
    source_hashes: impl Iterator<Item = [u8; 20]>,
) -> [u8; 20] {
    let mut keyed = cache_tag().into_bytes();
    keyed.push(b'/');
    keyed.extend_from_slice(flavor.as_bytes());
    for name in module_names {
        keyed.push(0);
        keyed.extend_from_slice(name.as_bytes());
    }
    keyed.push(1);
    for h in source_hashes {
        keyed.extend_from_slice(&h);
    }
    sha1(&keyed)
}

/// SHA-1 of arbitrary bytes, for callers assembling a [`context_key`].
pub fn content_hash(bytes: &[u8]) -> [u8; 20] {
    sha1(bytes)
}

/// Where the shared context seeds live: one directory per user, because a
/// context (the standard library plus a set of dependencies) is shared by
/// every program that imports it, unlike the per-entry `.ppcache`.
fn context_dir() -> Option<PathBuf> {
    let base = std::env::var_os("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cache")))?;
    Some(base.join("prepoly"))
}

fn context_file(key: &[u8; 20]) -> Option<PathBuf> {
    let hex: String = key.iter().map(|b| format!("{b:02x}")).collect();
    Some(context_dir()?.join(format!("ctx-{hex}.ppctx")))
}

/// Load the context seed for `key`, `None` when absent, foreign, or from
/// another compiler build.
pub fn load_context(key: &[u8; 20]) -> Option<prepoly_typeck::ContextTables> {
    let bytes = std::fs::read(context_file(key)?).ok()?;
    let rest = bytes.strip_prefix(MAGIC.as_slice())?;
    let n = *rest.first()? as usize;
    let tag = std::str::from_utf8(rest.get(1..1 + n)?).ok()?;
    if tag != cache_tag() {
        return None;
    }
    postcard::from_bytes(rest.get(1 + n..)?).ok()
}

/// Write the context seed for `key`, best-effort and atomic like [`save`].
pub fn save_context(key: &[u8; 20], seed: &prepoly_typeck::ContextTables) {
    let Some(path) = context_file(key) else {
        return;
    };
    let Some(dir) = path.parent() else { return };
    if std::fs::create_dir_all(dir).is_err() {
        return;
    }
    let Ok(body) = postcard::to_stdvec(seed) else {
        return;
    };
    let tag = cache_tag();
    let mut bytes = Vec::with_capacity(MAGIC.len() + 1 + tag.len() + body.len());
    bytes.extend_from_slice(MAGIC);
    bytes.push(tag.len() as u8);
    bytes.extend_from_slice(tag.as_bytes());
    bytes.extend_from_slice(&body);
    let tmp = path.with_extension("ppctx.tmp");
    if std::fs::write(&tmp, &bytes).is_ok() {
        let _ = std::fs::rename(&tmp, &path);
    }
}
