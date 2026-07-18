//! Filesystem queries behind the `Path` type, as a native Brass plugin.
//!
//! `std/path.cz` owns everything that is pure string manipulation --
//! splitting, joining, normalizing, relativizing -- and calls in here only for
//! the questions that need the operating system: what the working directory is,
//! and what actually exists on disk.
//!
//! Every function takes and returns a path as a `String`. A query about a path
//! that does not exist is `false` rather than an error, because "is this a
//! directory?" has a truthful answer for a name with nothing behind it.

use std::fs;
use std::path::Path;

use brass_plugin::{BrassLib, Registry, brass_lib, decl, export};

export! {
    /// The process's current working directory, as an absolute path.
    fn path_current_dir() -> Result<String, String> {
        to_string(std::env::current_dir().map_err(|e| e.to_string())?)
    }

    /// The user's home directory (`$HOME`, or `%USERPROFILE%` on Windows).
    fn path_home_dir() -> Result<String, String> {
        std::env::var("HOME")
            .or_else(|_| std::env::var("USERPROFILE"))
            .map_err(|_| "no home directory is set in the environment".to_string())
    }

    /// The directory for temporary files.
    fn path_temp_dir() -> Result<String, String> {
        to_string(std::env::temp_dir())
    }

    /// Whether anything exists at `p` (following a symbolic link).
    fn path_exists(p: String) -> bool {
        Path::new(&p).exists()
    }

    /// Whether `p` exists and is a directory (following a symbolic link).
    fn path_is_dir(p: String) -> bool {
        Path::new(&p).is_dir()
    }

    /// Whether `p` exists and is a regular file (following a symbolic link).
    fn path_is_file(p: String) -> bool {
        Path::new(&p).is_file()
    }

    /// Whether `p` itself is a symbolic link. The link is not followed, so this
    /// is true even when it dangles -- unlike `path_is_file`/`path_is_dir`,
    /// which answer about the target.
    fn path_is_symlink(p: String) -> bool {
        fs::symlink_metadata(&p).map(|m| m.is_symlink()).unwrap_or(false)
    }

    /// The canonical absolute path of `p`: every symbolic link resolved and
    /// every `.`/`..` removed. Requires that `p` exist.
    fn path_canonicalize(p: String) -> Result<String, String> {
        to_string(fs::canonicalize(&p).map_err(|e| format!("{p}: {e}"))?)
    }

    /// The path a symbolic link points at, exactly as it was stored -- possibly
    /// relative to the link's own directory, and possibly nonexistent.
    fn path_read_link(p: String) -> Result<String, String> {
        to_string(fs::read_link(&p).map_err(|e| format!("{p}: {e}"))?)
    }

    /// The names of the entries in directory `p`, in the order the operating
    /// system reports them (which is not sorted). `.` and `..` are not included.
    fn path_read_dir(p: String) -> Result<Vec<String>, String> {
        let mut names = Vec::new();
        for entry in fs::read_dir(&p).map_err(|e| format!("{p}: {e}"))? {
            let entry = entry.map_err(|e| format!("{p}: {e}"))?;
            names.push(
                entry
                    .file_name()
                    .into_string()
                    .map_err(|n| format!("{p}: entry name is not valid UTF-8: {n:?}"))?,
            );
        }
        Ok(names)
    }

    /// The size of the file at `p` in bytes.
    fn path_file_size(p: String) -> Result<i64, String> {
        let len = fs::metadata(&p).map_err(|e| format!("{p}: {e}"))?.len();
        i64::try_from(len).map_err(|_| format!("{p}: size does not fit in an int64"))
    }
}

/// A path back to Brass. Brass strings are UTF-8, so a path that is not
/// (legal on Unix, where a path is any byte string) is a reportable error rather
/// than a silent replacement-character mangling.
fn to_string(path: std::path::PathBuf) -> Result<String, String> {
    path.into_os_string()
        .into_string()
        .map_err(|p| format!("path is not valid UTF-8: {p:?}"))
}

struct PathLib;

impl BrassLib for PathLib {
    fn entry(reg: &mut Registry) {
        reg.export(decl!(path_current_dir));
        reg.export(decl!(path_home_dir));
        reg.export(decl!(path_temp_dir));
        reg.export(decl!(path_exists));
        reg.export(decl!(path_is_dir));
        reg.export(decl!(path_is_file));
        reg.export(decl!(path_is_symlink));
        reg.export(decl!(path_canonicalize));
        reg.export(decl!(path_read_link));
        reg.export(decl!(path_read_dir));
        reg.export(decl!(path_file_size));
    }
}

brass_lib!(PathLib);
