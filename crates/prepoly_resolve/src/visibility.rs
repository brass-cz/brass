//! Visibility rules. A name beginning with `_` is private
//! to its defining module; a file whose name begins with `_` is itself private
//! and cannot be imported.

/// Whether a top-level name is importable from another module.
pub fn is_public(name: &str) -> bool {
    !name.starts_with('_')
}

/// Whether a module (by path, last segment = file stem) is private.
pub fn is_private_module(path: &[String]) -> bool {
    path.last().map(|s| s.starts_with('_')).unwrap_or(false)
}
