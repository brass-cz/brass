//! The on-disk analysis cache (`.czcache`), shared by the `brass` driver and
//! the `czls` language server.
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
//! A cache is written next to its entry file (`app.cz` -> `app.czcache`), only
//! after an analysis with NO diagnostics, and names every source file that went
//! into the build. It is reused only when every one of those files still has
//! the same contents (length and SHA-1 -- see `FileStamp`), the compiler tag
//! matches, the entry file itself is the one recorded (the first dep -- so
//! `app` and `app.cz`, which share a cache path, cannot revive each other's
//! program), and the set of declared `BRASS_PACKAGES` names is unchanged (a
//! name newly bound captures an import's first segment BEFORE any file search,
//! so the same on-disk files no longer describe the same program). Source
//! files are named RELATIVE to the root each was resolved under (the entry
//! file's directory, an include root, a package root), never by machine path
//! -- so a cache survives the whole project moving. Native plugin libraries
//! are the exception: the synthesized wrapper embeds the library's absolute
//! path (the runtime dlopens exactly that string), so their stamps are pinned
//! `Absolute` and a cache involving plugins misses after a move instead of
//! re-lowering wrappers that would open the old location. Any mismatch, short
//! read, or decode error falls back to the full pipeline -- the cache can
//! never make a build wrong, only faster.
//!
//! Known accepted limit: a module served by an include-root file at save time
//! that a native plugin under an EARLIER root would now shadow (or the
//! reverse, a project `.cz` newly shadowing a plugin) is not re-judged by the
//! stamps; the wrapper/file distinction is only re-checked through the entry
//! and package guards above.
//!
//! The format is binary (postcard: varint-packed serde, no field names), chosen
//! for load speed and size; it is not meant to be read by humans, and no
//! compatibility across compiler versions is attempted -- the header pins both
//! the format and the compiler version, and anything else is discarded.

use std::path::{Path, PathBuf};

use brass_hir::{LoadedModule, Type};
use brass_metadata::{BuildChannel, compiler_tag};
use brass_parser::Span;

/// Bumped whenever the payload layout changes, so an old file is discarded by
/// the header check instead of misread by postcard (which carries no schema).
pub const FORMAT_VERSION: u16 = 3;

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
    /// Relative to SOME include root; validation walks the current
    /// `BRASS_INCLUDE` roots in resolution order and judges the first
    /// candidate that exists -- exactly the shadowing the loader itself
    /// would apply.
    Include(String),
    /// Relative to the named `BRASS_PACKAGES` package's root. The standard
    /// library is the package named `std` (bound implicitly by a distributed
    /// toolchain), so its sources stamp as `Package("std", ...)`.
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
    pub search: &'a brass_resolve::SearchPaths,
}

impl<'a> StampRoots<'a> {
    pub fn new(entry: &Path, search: &'a brass_resolve::SearchPaths) -> StampRoots<'a> {
        // A bare filename entry (`brass main.cz`) has `Some("")` as its parent,
        // which neither canonicalizes nor joins usefully; it means the CWD.
        let dir = match entry.parent() {
            Some(p) if !p.as_os_str().is_empty() => p,
            _ => Path::new("."),
        };
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
        Some(Self::of_content(path, &bytes, roots))
    }

    /// Stamp `path` with `content` standing in for the file's bytes: the text
    /// the compiler actually PARSED, not a re-read of the file. Re-reading at
    /// save time races an editor writing during the (long) analysis -- the new
    /// content's hash would be attached to the old content's analysis and every
    /// later run would hit a permanently stale cache.
    pub fn of_text(path: &Path, content: &str, roots: &StampRoots) -> FileStamp {
        Self::of_content(path, content.as_bytes(), roots)
    }

    fn of_content(path: &Path, bytes: &[u8], roots: &StampRoots) -> FileStamp {
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
        // A native plugin library is pinned to its absolute path: the
        // synthesized wrapper in the cached AST embeds this exact string as
        // the runtime's dlopen target, so validating the stamp anywhere else
        // would re-lower wrappers that open the OLD location.
        let relocatable = !matches!(
            canon.extension().and_then(|e| e.to_str()),
            Some("so" | "dylib" | "dll")
        );
        let origin = if !relocatable {
            StampOrigin::Absolute(canon.display().to_string())
        } else if let Some(rel) = rel_under(&roots.entry_dir) {
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
        FileStamp {
            origin,
            len: bytes.len() as u64,
            sha1: sha1(bytes),
        }
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
    pub sum_views: Vec<(Span, Type)>,
    pub call_locations: Vec<(Span, (String, u32, u32))>,
    pub lift_errs: Vec<Span>,
    pub fields_loops: Vec<(Span, Vec<String>)>,
    pub type_names: Vec<(Span, String)>,
    pub typeof_types: Vec<(Span, Type)>,
    pub null_props: Vec<Span>,
}

/// Everything a `.czcache` stores.
#[derive(serde::Serialize, serde::Deserialize)]
pub struct Payload {
    /// Every on-disk source the build read. The FIRST stamp is the entry
    /// file's: on load its content is compared against the file the user
    /// actually named, so two entries sharing one cache path (`app` and
    /// `app.cz` both map to `app.czcache`) can never revive each other's
    /// program, and `brass app.czcache` misses instead of executing itself.
    pub deps: Vec<FileStamp>,
    /// The `BRASS_PACKAGES` names declared when the cache was written
    /// (sorted). A declared name binds an import's first segment BEFORE any
    /// file search, so a changed name set can re-route imports while every
    /// stamped file is untouched; any difference is a miss. Names only --
    /// paths would break relocation, and a package's CONTENT is already
    /// covered by its stamps.
    pub packages: Vec<String>,
    /// The final module graph: post-resolution, post-rewrite, post-keyed
    /// specialization. Re-lowering these reproduces the checked program.
    pub modules: Vec<LoadedModule>,
    /// Diagnostics the full pipeline prints for a CLEAN program (the spawn
    /// auto-acquire notes); replayed on a hit so warm runs warn identically.
    pub warnings: Vec<String>,
    pub channels: Channels,
}

/// The cache path for an entry file: `app.cz` -> `app.czcache`, next to it.
/// An extensionless entry (a `#!` script such as `czpm`) gains the extension.
pub fn cache_path(entry: &Path) -> PathBuf {
    entry.with_extension("czcache")
}

/// The tag written into the header: the compiler's identity
/// ([`brass_metadata::compiler_tag`] -- version, channel, commit), the payload
/// format version, and the caller's `flavor` -- the front-end configuration
/// whose rewrite passes shape the cached ASTs (the JIT driver auto-acquires
/// `spawn` bodies; a REPL-only driver does not), so two differently-configured
/// binaries of the same compiler never accept each other's caches -- plus, for
/// a working-tree build ONLY, the running executable's modification time.
///
/// A released compiler (a channel the release workflow stamped) is fully
/// identified by its channel and commit, so its tag is the same on every machine
/// that installs that release: a `.czcache` written when the libraries are
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
/// megabytes; a local rebuild always moves it. A nightly build whose own mtime
/// cannot be determined gets NO tag at all -- caching is skipped rather than
/// letting two such builds silently share one.
fn cache_tag(flavor: &str) -> Option<String> {
    let tag = format!("{}/{}/{flavor}", compiler_tag(), FORMAT_VERSION);
    if brass_metadata::build_channel() != BuildChannel::Nightly {
        return Some(tag);
    }
    Some(format!("{tag}/{}", exe_mtime_nanos()?))
}

fn exe_mtime_nanos() -> Option<u128> {
    let exe = std::env::current_exe().ok()?;
    let mtime = std::fs::metadata(exe).ok()?.modified().ok()?;
    Some(mtime.duration_since(std::time::UNIX_EPOCH).ok()?.as_nanos())
}

/// Whether caching is enabled at all (`BRASS_CACHE=off`/`0` disables it,
/// for debugging and for tests that must exercise the full pipeline).
pub fn enabled() -> bool {
    !matches!(std::env::var("BRASS_CACHE").as_deref(), Ok("off") | Ok("0"))
}

/// Frame `body` with the header every cache file shares: magic, length-prefixed
/// tag, and the body's SHA-1 -- postcard is positional varint data with no
/// checksum of its own, so a corrupted body could otherwise decode into a
/// shape-valid payload whose stamps still validate.
fn encode_file(tag: &str, body: &[u8]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(MAGIC.len() + 1 + tag.len() + 20 + body.len());
    bytes.extend_from_slice(MAGIC);
    bytes.push(tag.len() as u8);
    bytes.extend_from_slice(tag.as_bytes());
    bytes.extend_from_slice(&sha1(body));
    bytes.extend_from_slice(body);
    bytes
}

/// The body of a cache file whose magic, tag, and body checksum all match;
/// `None` rejects foreign, stale-versioned, or corrupted files before any
/// payload decoding.
fn decode_file<'a>(bytes: &'a [u8], tag: &str) -> Option<&'a [u8]> {
    let rest = bytes.strip_prefix(MAGIC.as_slice())?;
    let n = *rest.first()? as usize;
    if std::str::from_utf8(rest.get(1..1 + n)?).ok()? != tag {
        return None;
    }
    let checksum: &[u8; 20] = rest.get(1 + n..1 + n + 20)?.try_into().ok()?;
    let body = rest.get(1 + n + 20..)?;
    (sha1(body) == *checksum).then_some(body)
}

/// Write `bytes` to `path` through a uniquely-named temporary file and a
/// rename, best-effort: the cache is an accelerator, never a requirement, and
/// two concurrent writers publish whole files instead of interleaving into one
/// shared temp name.
fn write_atomic(path: &Path, bytes: &[u8]) {
    static NEXT_TMP: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let mut tmp = path.as_os_str().to_owned();
    tmp.push(format!(
        ".tmp{}-{}",
        std::process::id(),
        NEXT_TMP.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    let tmp = PathBuf::from(tmp);
    if std::fs::write(&tmp, bytes).is_err() {
        return;
    }
    // Windows does not replace an existing destination with `rename`. A brief
    // missing-file window is safe for this best-effort cache: readers fall back
    // to analysis, while every published file remains whole.
    #[cfg(windows)]
    if path.is_file() {
        let _ = std::fs::remove_file(path);
    }
    if std::fs::rename(&tmp, path).is_err() {
        let _ = std::fs::remove_file(&tmp);
    }
}

/// The current sorted `BRASS_PACKAGES` name set, the payload's `packages`
/// guard on both save and load.
pub fn package_names(search: &brass_resolve::SearchPaths) -> Vec<String> {
    let mut names: Vec<String> = search.packages.keys().cloned().collect();
    names.sort();
    names
}

/// Load and validate the cache for `entry` under the current resolution roots.
/// `None` -- silently, the caller falls back to the full pipeline -- when the
/// file is missing, foreign, from another compiler version, format, or front
/// end `flavor`, the entry file is not the recorded one, the declared package
/// names changed, or any recorded source reference now resolves to different
/// contents.
pub fn load(entry: &Path, flavor: &str, search: &brass_resolve::SearchPaths) -> Option<Payload> {
    let roots = StampRoots::new(entry, search);
    let path = cache_path(entry);
    let bytes = std::fs::read(&path).ok()?;
    let body = decode_file(&bytes, &cache_tag(flavor)?)?;
    let payload: Payload = postcard::from_bytes(body).ok()?;
    // The first dep must BE the file the user named: same length, same hash.
    // `still_valid` alone would only prove the recorded file exists somewhere.
    let entry_bytes = std::fs::read(entry).ok()?;
    let first = payload.deps.first()?;
    if first.len != entry_bytes.len() as u64 || first.sha1 != sha1(&entry_bytes) {
        tracing::debug!(target: "brass::perf", "cache: entry is not the recorded one, ignoring {}", path.display());
        return None;
    }
    if payload.packages != package_names(search) {
        tracing::debug!(target: "brass::perf", "cache: BRASS_PACKAGES names changed, ignoring {}", path.display());
        return None;
    }
    for dep in &payload.deps {
        if !dep.still_valid(&roots) {
            tracing::debug!(target: "brass::perf", "cache: {:?} changed, ignoring {}", dep.origin, path.display());
            return None;
        }
    }
    Some(payload)
}

/// A PARTIAL analysis cache: what a stopped lazy run had settled when its
/// program ended -- a `brass_typeck::stream::StreamSnapshot` under the same
/// validity guards as the full [`Payload`] (compiler tag via the header,
/// entry identity, package names, every recorded source unchanged). The
/// next lazy run resumes checking from it; it never stands in for a full
/// analysis (its flavor tag keeps [`load`] from ever accepting it).
#[derive(serde::Serialize, serde::Deserialize)]
pub struct PartialPayload {
    pub deps: Vec<FileStamp>,
    pub packages: Vec<String>,
    pub snapshot: brass_typeck::stream::StreamSnapshot,
}

/// [`load`] for a partial payload (same validation, its own flavor tag).
pub fn load_partial(
    entry: &Path,
    flavor: &str,
    search: &brass_resolve::SearchPaths,
) -> Option<brass_typeck::stream::StreamSnapshot> {
    let roots = StampRoots::new(entry, search);
    let path = cache_path(entry);
    let bytes = std::fs::read(&path).ok()?;
    let body = decode_file(&bytes, &cache_tag(flavor)?)?;
    let payload: PartialPayload = postcard::from_bytes(body).ok()?;
    let entry_bytes = std::fs::read(entry).ok()?;
    let first = payload.deps.first()?;
    if first.len != entry_bytes.len() as u64 || first.sha1 != sha1(&entry_bytes) {
        return None;
    }
    if payload.packages != package_names(search) {
        return None;
    }
    for dep in &payload.deps {
        if !dep.still_valid(&roots) {
            tracing::debug!(target: "brass::perf", "partial cache: {:?} changed, ignoring", dep.origin);
            return None;
        }
    }
    tracing::debug!(target: "brass::perf", "partial cache: resuming from {}", path.display());
    Some(payload.snapshot)
}

/// [`save`] for a partial payload (its own flavor tag, same file).
pub fn save_partial(entry: &Path, flavor: &str, payload: &PartialPayload) {
    let (Ok(body), Some(tag)) = (postcard::to_stdvec(payload), cache_tag(flavor)) else {
        return;
    };
    write_atomic(&cache_path(entry), &encode_file(&tag, &body));
}

/// Write the cache for `entry`, best-effort (see [`write_atomic`]).
pub fn save(entry: &Path, flavor: &str, payload: &Payload) {
    let (Ok(body), Some(tag)) = (postcard::to_stdvec(payload), cache_tag(flavor)) else {
        return;
    };
    write_atomic(&cache_path(entry), &encode_file(&tag, &body));
}

// ===== the context seed cache (`.czctx`) =====

/// The key of a context (every module of a program except its entry): the
/// compiler tag, the module names in load order, and the SHA-1 of every source
/// text that is not the entry's -- so any change of content, name, or order is
/// a different context, while the entry changing (which shifts every later
/// span) is not. `flavor` distinguishes front ends whose rewrite passes differ
/// (the driver auto-acquires `spawn` bodies; the language server does not), so
/// each seeds its own entry rather than consuming tables built over different
/// ASTs. `None` when this build cannot form a tag (see [`cache_tag`]).
pub fn context_key(
    flavor: &str,
    module_names: impl Iterator<Item = String>,
    source_hashes: impl Iterator<Item = [u8; 20]>,
) -> Option<[u8; 20]> {
    let mut keyed = cache_tag(flavor)?.into_bytes();
    for name in module_names {
        keyed.push(0);
        keyed.extend_from_slice(name.as_bytes());
    }
    keyed.push(1);
    for h in source_hashes {
        keyed.extend_from_slice(&h);
    }
    Some(sha1(&keyed))
}

/// SHA-1 of arbitrary bytes, for callers assembling a [`context_key`].
pub fn content_hash(bytes: &[u8]) -> [u8; 20] {
    sha1(bytes)
}

/// Where the shared context seeds live: one directory per user, because a
/// context (the standard library plus a set of dependencies) is shared by
/// every program that imports it, unlike the per-entry `.czcache`.
fn context_dir() -> Option<PathBuf> {
    let base = std::env::var_os("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cache")))?;
    Some(base.join("brass"))
}

fn context_file(key: &[u8; 20]) -> Option<PathBuf> {
    let hex: String = key.iter().map(|b| format!("{b:02x}")).collect();
    Some(context_dir()?.join(format!("ctx-{hex}.czctx")))
}

/// Load the context seed for `key`, `None` when absent, foreign, corrupted,
/// or from another compiler build. The key already encodes the flavor, so the
/// in-file tag echo only needs the compiler identity; the neutral flavor
/// keeps it uniform.
pub fn load_context(key: &[u8; 20]) -> Option<brass_typeck::ContextTables> {
    let bytes = std::fs::read(context_file(key)?).ok()?;
    let body = decode_file(&bytes, &cache_tag("ctx")?)?;
    postcard::from_bytes(body).ok()
}

/// Write the context seed for `key`, best-effort and atomic like [`save`].
pub fn save_context(key: &[u8; 20], seed: &brass_typeck::ContextTables) {
    let Some(path) = context_file(key) else {
        return;
    };
    let Some(dir) = path.parent() else { return };
    if std::fs::create_dir_all(dir).is_err() {
        return;
    }
    let (Ok(body), Some(tag)) = (postcard::to_stdvec(seed), cache_tag("ctx")) else {
        return;
    };
    write_atomic(&path, &encode_file(&tag, &body));
}

/// The incremental-rebuild sidecar of a context seed: the seed together with
/// each context module's source hash. Stored under the context's IDENTITY
/// (its module-path list, contents excluded), so an edit finds the previous
/// build of the SAME context, diffs the per-module hashes, and re-infers
/// only the changed modules and their importers against the retained rest
/// (see the driver's `cached_context_seed`).
#[derive(serde::Serialize, serde::Deserialize)]
pub struct ContextBundle {
    /// Dotted module path -> content hash of its source, in load order.
    pub module_hashes: Vec<(String, [u8; 20])>,
    pub seed: brass_typeck::ContextTables,
}

fn context_bundle_file(id: &[u8; 20]) -> Option<PathBuf> {
    let hex: String = id.iter().map(|b| format!("{b:02x}")).collect();
    Some(context_dir()?.join(format!("ctxb-{hex}.czctx")))
}

/// Load the incremental sidecar for the context identity `id`; `None` when
/// absent, foreign, corrupted, or from another compiler build.
pub fn load_context_bundle(id: &[u8; 20]) -> Option<ContextBundle> {
    let bytes = std::fs::read(context_bundle_file(id)?).ok()?;
    let body = decode_file(&bytes, &cache_tag("ctxb")?)?;
    postcard::from_bytes(body).ok()
}

/// Write the incremental sidecar, best-effort and atomic like [`save`].
pub fn save_context_bundle(id: &[u8; 20], bundle: &ContextBundle) {
    let Some(path) = context_bundle_file(id) else {
        return;
    };
    let Some(dir) = path.parent() else { return };
    if std::fs::create_dir_all(dir).is_err() {
        return;
    }
    let (Ok(body), Some(tag)) = (postcard::to_stdvec(bundle), cache_tag("ctxb")) else {
        return;
    };
    write_atomic(&path, &encode_file(&tag, &body));
}
