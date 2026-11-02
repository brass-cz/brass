//! Ownership input independent of selection and source loading.

use crate::{ModuleSource, SourceOrigin};
use std::path::{Path, PathBuf};

/// The source package whose bodies must be checked, including unimported files.
/// An explicit CLI project root wins. Otherwise czpm supplies its manifest-root
/// working directory; a bare file owns its entry and local-route imports. The
/// caller canonicalizes paths once. Dependency/include/plugin routes remain
/// external even below the package root; an explicitly opened entry is own.
#[derive(Clone, Debug)]
pub struct ProjectScope {
    /// Explicitly opened source, always owned regardless of its resolver route.
    pub entry: PathBuf,
    /// CLI root or czpm's manifest directory; absent for a bare source file.
    pub package_root: Option<PathBuf>,
}

impl ProjectScope {
    /// Combine an explicit root with the caller's manifest-directory evidence.
    pub fn new(entry: PathBuf, explicit: Option<PathBuf>, manifest_dir: Option<PathBuf>) -> Self {
        Self {
            entry,
            package_root: explicit.or(manifest_dir),
        }
    }

    /// Classify captured provenance without reinterpreting dependency paths.
    pub fn owns(&self, source: &ModuleSource) -> bool {
        source.location == self.entry
            || (matches!(source.origin, SourceOrigin::Own(_))
                && self
                    .package_root
                    .as_ref()
                    .is_none_or(|root| source.location.starts_with(root)))
    }

    /// Whether a separately enumerated source belongs to the package. Resolver
    /// roots take precedence over physical containment, including vendored deps.
    pub fn owns_unloaded(&self, path: &Path, dependency_roots: &[PathBuf]) -> bool {
        path == self.entry
            || (self
                .package_root
                .as_ref()
                .is_some_and(|root| path.starts_with(root))
                && !dependency_roots.iter().any(|root| path.starts_with(root)))
    }
}
