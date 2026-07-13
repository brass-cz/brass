//! File descriptors and byte I/O, as a native prepoly plugin.
//!
//! `libraries/fs.pp` builds the `File` surface on these primitives. A file
//! crosses the boundary as its raw descriptor (an `i64`); everything that is
//! policy rather than I/O -- which descriptor a `File` holds, the double-close
//! guard, size lookups (delegated to the path library, which stats by name) --
//! lives on the prepoly side. The descriptor is borrowed without ownership for
//! reads/writes/seeks (so an operation does not close it); `fd_close` takes
//! ownership and closes it.
//!
//! Directories are not descriptors: `dir_create`/`dir_remove` work by name, so
//! they take a path and hand back nothing.

use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::mem::ManuallyDrop;
use std::os::fd::{FromRawFd, IntoRawFd, RawFd};

use prepoly_plugin::{Bytes, PrepolyLib, Registry, decl, export, prepoly_lib};

/// Reject a negative descriptor (a closed `File` stores -1) before it can
/// hit `from_raw_fd`'s assertion; the caller sees an ordinary error Result.
fn live(fd: i64) -> Result<(), String> {
    if fd < 0 {
        return Err("file is closed".to_string());
    }
    Ok(())
}

/// Run `op` on the `File` for `fd` without taking ownership, so the borrow
/// ending does not close the descriptor.
fn borrow_fd<R>(fd: i64, op: impl FnOnce(&mut File) -> R) -> R {
    let mut file = ManuallyDrop::new(unsafe { File::from_raw_fd(fd as RawFd) });
    op(&mut file)
}

/// Copy the tree rooted at `source` into `target`, which the caller has checked
/// does not exist yet.
///
/// A symbolic link inside the tree is RECREATED as a link rather than followed.
/// That is what POSIX's `cp -R` does, and it is also what keeps the walk finite:
/// following a link that points at an ancestor would recurse forever.
fn copy_tree(source: &std::path::Path, target: &std::path::Path) -> std::io::Result<()> {
    std::fs::create_dir_all(target)?;
    for entry in std::fs::read_dir(source)? {
        let entry = entry?;
        let from = entry.path();
        let to = target.join(entry.file_name());
        let kind = entry.file_type()?;
        if kind.is_symlink() {
            std::os::unix::fs::symlink(std::fs::read_link(&from)?, &to)?;
        } else if kind.is_dir() {
            copy_tree(&from, &to)?;
        } else {
            std::fs::copy(&from, &to)?;
        }
    }
    Ok(())
}

/// Check the invariants both directory operations share, and answer the pair of
/// paths to work with: `source` must be a directory, `target` must not exist at
/// all (see `libraries/fs.pp` on why an existing target is refused rather than
/// replaced), and `target` must not lie INSIDE `source` -- copying a tree into
/// itself would never terminate.
fn checked_dirs(source: &str, target: &str) -> Result<(), String> {
    let meta = std::fs::metadata(source).map_err(|e| format!("{source}: {e}"))?;
    if !meta.is_dir() {
        return Err(format!("{source} is not a directory"));
    }
    if std::path::Path::new(target).exists() {
        return Err(format!("{target} already exists"));
    }
    // Compare the source's real location with the target's would-be one: the
    // target does not exist, so only its parent can be canonicalized.
    let src = std::fs::canonicalize(source).map_err(|e| format!("{source}: {e}"))?;
    let dst_parent = std::path::Path::new(target)
        .parent()
        .unwrap_or(std::path::Path::new("."));
    let dst = std::fs::canonicalize(dst_parent)
        .map_err(|e| format!("{}: {e}", dst_parent.display()))?
        .join(std::path::Path::new(target).file_name().unwrap_or_default());
    if dst.starts_with(&src) {
        return Err(format!("{target} is inside {source}"));
    }
    Ok(())
}

export! {
    /// Open the file at `path` and give up its descriptor. Modes: `r` read,
    /// `w` truncate+create write, `a` append+create. The prepoly side owns
    /// the descriptor from here.
    fn fd_open(path: String, mode: String) -> Result<i64, String> {
        let mut opts = OpenOptions::new();
        match mode.as_str() {
            "r" => opts.read(true),
            "w" => opts.write(true).create(true).truncate(true),
            "a" => opts.append(true).create(true),
            other => return Err(format!("invalid open mode `{other}`")),
        };
        match opts.open(&path) {
            Ok(f) => Ok(i64::from(f.into_raw_fd())),
            Err(e) => Err(e.to_string()),
        }
    }

    /// Up to `n` bytes from descriptor `fd` (fewer at end-of-file).
    fn fd_read(fd: i64, n: i64) -> Result<Bytes, String> {
        live(fd)?;
        let mut buf = vec![0u8; n.max(0) as usize];
        match borrow_fd(fd, |f| f.read(&mut buf)) {
            Ok(got) => {
                buf.truncate(got);
                Ok(Bytes(buf))
            }
            Err(e) => Err(e.to_string()),
        }
    }

    /// Write all of `data` to descriptor `fd`, returning its length.
    fn fd_write(fd: i64, data: Bytes) -> Result<i64, String> {
        live(fd)?;
        match borrow_fd(fd, |f| f.write_all(&data.0)) {
            Ok(()) => Ok(data.0.len() as i64),
            Err(e) => Err(e.to_string()),
        }
    }

    /// Move descriptor `fd`'s read/write cursor to absolute byte offset `pos`
    /// from the start of the file.
    fn fd_seek(fd: i64, pos: i64) -> Result<(), String> {
        live(fd)?;
        borrow_fd(fd, |f| f.seek(SeekFrom::Start(pos.max(0) as u64)))
            .map(|_| ())
            .map_err(|e| e.to_string())
    }

    /// Close descriptor `fd`. The standard streams 0/1/2 are left open (a
    /// backstop under `File.close`'s own guard), as closing them would break
    /// the process.
    fn fd_close(fd: i64) -> Result<(), String> {
        if fd > 2 {
            drop(unsafe { File::from_raw_fd(fd as RawFd) });
        }
        Ok(())
    }

    /// Delete the file at `path`. A symbolic link is removed as the LINK (what
    /// it points at is untouched). A `path` that is a directory is an error --
    /// `dir_remove` is the call that takes a tree -- and so is one that is not
    /// there, so a typo in a destructive call cannot read as done.
    fn file_remove(path: String) -> Result<(), String> {
        std::fs::remove_file(&path).map_err(|e| format!("{path}: {e}"))
    }

    /// Copy the contents and permission bits of `source` onto `target`,
    /// replacing `target` when it already exists. `target`'s parent directory
    /// must exist (`dir_create` makes one); a directory as either side is an
    /// error.
    fn file_copy(source: String, target: String) -> Result<(), String> {
        std::fs::copy(&source, &target)
            .map(|_| ())
            .map_err(|e| format!("{source} -> {target}: {e}"))
    }

    /// Move the file at `source` to `target`, replacing `target` when it
    /// already exists.
    ///
    /// A rename is atomic but cannot cross filesystems, and a temporary
    /// directory very often IS another filesystem -- so a plain rename would
    /// fail exactly where "move the file I just built in /tmp into place" is
    /// the point. On that one error the move falls back to a copy followed by a
    /// delete: no longer atomic, and `source` survives if the delete fails, but
    /// it does what the caller asked. Every other error is reported as it is.
    fn file_move(source: String, target: String) -> Result<(), String> {
        // A directory would be renamed happily on one filesystem and fail the
        // copy fallback on another; refuse it here so the name does not lie
        // about what it moves.
        if std::fs::metadata(&source)
            .map_err(|e| format!("{source}: {e}"))?
            .is_dir()
        {
            return Err(format!("{source} is a directory, not a file"));
        }
        match std::fs::rename(&source, &target) {
            Ok(()) => Ok(()),
            Err(e) if e.kind() == std::io::ErrorKind::CrossesDevices => {
                std::fs::copy(&source, &target)
                    .map_err(|e| format!("{source} -> {target}: {e}"))?;
                std::fs::remove_file(&source).map_err(|e| {
                    format!("{source} was copied to {target} but could not be removed: {e}")
                })
            }
            Err(e) => Err(format!("{source} -> {target}: {e}")),
        }
    }

    /// Copy the directory tree at `source` to `target`, which must not exist.
    /// A symbolic link inside the tree is recreated as a link, not followed.
    fn dir_copy(source: String, target: String) -> Result<(), String> {
        checked_dirs(&source, &target)?;
        copy_tree(std::path::Path::new(&source), std::path::Path::new(&target))
            .map_err(|e| format!("{source} -> {target}: {e}"))
    }

    /// Move the directory tree at `source` to `target`, which must not exist.
    ///
    /// A rename when the two sit on one filesystem (atomic, and nothing is
    /// read); a copy of the tree followed by its removal when they do not,
    /// since a rename cannot cross filesystems. The fallback is not atomic, and
    /// `source` survives if the removal fails -- the error says so.
    fn dir_move(source: String, target: String) -> Result<(), String> {
        checked_dirs(&source, &target)?;
        match std::fs::rename(&source, &target) {
            Ok(()) => Ok(()),
            Err(e) if e.kind() == std::io::ErrorKind::CrossesDevices => {
                copy_tree(std::path::Path::new(&source), std::path::Path::new(&target))
                    .map_err(|e| format!("{source} -> {target}: {e}"))?;
                std::fs::remove_dir_all(&source).map_err(|e| {
                    format!("{source} was copied to {target} but could not be removed: {e}")
                })
            }
            Err(e) => Err(format!("{source} -> {target}: {e}")),
        }
    }

    /// Create the directory at `path` along with every missing parent, as
    /// `mkdir -p` does. An existing directory is not an error (the requested
    /// state already holds); a `path` that exists as a file is.
    fn dir_create(path: String) -> Result<(), String> {
        std::fs::create_dir_all(&path).map_err(|e| format!("{path}: {e}"))
    }

    /// Remove the directory at `path` and everything under it, recursively.
    /// A symbolic link inside is removed as a link -- the walk does not follow
    /// it, so the target is untouched. `path` itself must be a directory: a
    /// symlink to one is not removed through here (nor is its target), and a
    /// missing `path` is an error rather than a silent success, so a typo in a
    /// destructive call does not read as done.
    fn dir_remove(path: String) -> Result<(), String> {
        std::fs::remove_dir_all(&path).map_err(|e| format!("{path}: {e}"))
    }
}

struct FsLib;

impl PrepolyLib for FsLib {
    fn entry(reg: &mut Registry) {
        reg.export(decl!(fd_open));
        reg.export(decl!(fd_read));
        reg.export(decl!(fd_write));
        reg.export(decl!(fd_seek));
        reg.export(decl!(fd_close));
        reg.export(decl!(file_remove));
        reg.export(decl!(file_copy));
        reg.export(decl!(file_move));
        reg.export(decl!(dir_copy));
        reg.export(decl!(dir_move));
        reg.export(decl!(dir_create));
        reg.export(decl!(dir_remove));
    }
}

prepoly_lib!(FsLib);
