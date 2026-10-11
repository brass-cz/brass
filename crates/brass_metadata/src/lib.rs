//! The identity of a compiler build: the workspace version, the release
//! channel, and the git commit it was built from.
//!
//! Every binary in the tree reports its version through [`version_string`], so
//! that all of them agree on what "this compiler" is. Nothing else should read
//! `CARGO_PKG_VERSION` directly: a per-crate version would drift from the one
//! the user sees, and a version alone cannot distinguish two builds of the same
//! release.

use std::sync::OnceLock;

/// The commit `git rev-parse HEAD` reported when this crate was compiled, or
/// `unknown` for a build made outside a git checkout.
pub const COMMIT_HASH: &str = env!("COMMIT_HASH");

/// Use [`build_channel`] function usually
pub const BUILD_CHANNEL: Option<&str> = option_env!("BUILD_CHANNEL");

const PACKAGE_VERSION: &str = env!("CARGO_PKG_VERSION");

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuildChannel {
    Stable,
    Beta,
    Nightly,
    Custom(String),
}
impl From<&str> for BuildChannel {
    fn from(value: &str) -> Self {
        match value {
            "stable" => Self::Stable,
            "beta" => Self::Beta,
            "nightly" => Self::Nightly,
            _ => Self::Custom(value.to_string()),
        }
    }
}
impl std::fmt::Display for BuildChannel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Stable => f.write_str("stable"),
            Self::Beta => f.write_str("beta"),
            Self::Nightly => f.write_str("nightly"),
            Self::Custom(v) => f.write_str(v),
        }
    }
}

/// BUILD_CHANNEL should only be set in release workflow
///
/// An empty value counts as unset: a CI expression that resolves to nothing
/// exports the variable as `""`, which must not be read back as a channel named
/// "".
pub fn build_channel() -> BuildChannel {
    match BUILD_CHANNEL {
        Some(v) if !v.is_empty() => BuildChannel::from(v),
        _ => BuildChannel::Nightly,
    }
}

/// The commit abbreviated the way version output shows it. Returns the whole
/// value when it is shorter than an abbreviation, i.e. `unknown`.
fn short_commit() -> &'static str {
    COMMIT_HASH.get(..7).unwrap_or(COMMIT_HASH)
}

/// Machine-readable compiler identity, including the full commit. Artifact
/// consumers compare this tag for equality; unstamped working-tree builds
/// additionally need a fingerprint of the running executable.
pub fn compiler_tag() -> String {
    format!("{}@{}-{}", PACKAGE_VERSION, build_channel(), COMMIT_HASH)
}

/// The version every Brass binary reports, e.g. `0.1.0 (nightly 8314ac1)`.
/// The channel and commit are part of it because the version alone identifies a
/// release, not a build: pre-release builds share the version of the release
/// they lead up to.
///
/// Cached and handed out as `&'static str` so that it can be given straight to a
/// `clap` command, which stores only borrowed strings.
pub fn version_string() -> &'static str {
    static VERSION: OnceLock<String> = OnceLock::new();
    VERSION.get_or_init(|| {
        format!(
            "{} ({} {})",
            PACKAGE_VERSION,
            build_channel(),
            short_commit()
        )
    })
}
