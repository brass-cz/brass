use std::collections::BTreeMap;
use std::path::Path;

use serde::Deserialize;

/// Top-level structure of `package.toml`.
#[derive(Deserialize)]
pub struct Manifest {
    pub package: PackageInfo,
    #[serde(default)]
    pub dependencies: BTreeMap<String, Dependency>,
}

#[derive(Deserialize)]
#[allow(dead_code)]
pub struct PackageInfo {
    pub name: String,
    #[serde(default)]
    pub author: String,
    #[serde(default)]
    pub license: String,
}

/// A single dependency entry, one of:
///
/// - `"name" = { git = "https://...", hash = "..." }` — cloned at that commit
///   into the shared package cache;
/// - `"name" = { path = "../package" }` — a local directory used in place,
///   resolved against the project root (the directory of `package.toml`).
#[derive(Deserialize)]
#[serde(try_from = "RawDependency")]
pub enum Dependency {
    Git { git: String, hash: String },
    Path { path: String },
}

/// The raw key set of a dependency table, validated into [`Dependency`] so a
/// wrong combination reports which key is missing or conflicting instead of
/// serde's generic no-variant-matched message.
#[derive(Deserialize)]
struct RawDependency {
    git: Option<String>,
    hash: Option<String>,
    path: Option<String>,
}

impl TryFrom<RawDependency> for Dependency {
    type Error = String;
    fn try_from(raw: RawDependency) -> Result<Dependency, String> {
        match (raw.git, raw.hash, raw.path) {
            (Some(git), Some(hash), None) => Ok(Dependency::Git { git, hash }),
            (None, None, Some(path)) => Ok(Dependency::Path { path }),
            (Some(_), None, None) => Err("a `git` dependency also needs a `hash`".into()),
            (None, Some(_), None) => Err("`hash` needs a `git` URL".into()),
            (None, None, None) => Err("a dependency needs `git` + `hash`, or `path`".into()),
            (_, _, Some(_)) => Err("`path` cannot be combined with `git`/`hash`".into()),
        }
    }
}

impl Manifest {
    pub fn load(path: &Path) -> Result<Manifest, String> {
        let content = std::fs::read_to_string(path)
            .map_err(|e| format!("cannot read `{}`: {e}", path.display()))?;
        toml::from_str(&content).map_err(|e| format!("cannot parse `{}`: {e}", path.display()))
    }
}
