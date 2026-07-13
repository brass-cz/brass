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
        reg.export(decl!(dir_create));
        reg.export(decl!(dir_remove));
    }
}

prepoly_lib!(FsLib);
