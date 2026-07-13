import std.collections.HashMap
import data.toml.TomlValue
import path.Path

/** A parsed `package.toml`. */
type Manifest = {
    package: PackageInfo
    dependencies: Dependencies
}

/** The `[package]` table. Every field is required. */
type PackageInfo = {
    name: string
    author: string
    license: string
}

/** The `[dependencies]` table, keyed by dependency name. */
type Dependencies = HashMap { key: string, value: Dependency }

/**
 * Where one dependency comes from. The variant is chosen by the keys the entry
 * carries, so the three sources stay mutually exclusive:
 *
 *     serde = "1.0"                          # Registry
 *     mylib = { version = "1.0" }            # Registry
 *     mylib = { git = "...", rev = "..." }   # Git
 *     mylib = { path = "../mylib" }          # Path
 */
type Dependency =
    | Registry { version: string }
    | Tarball { tarball: string }
    | Git { git: string, rev: string }
    | Path { path: Path }

/** The revision a `git` dependency tracks when it names none. */
const DEFAULT_REV = "HEAD"

/**
 * Parse a manifest, or report the first problem found.
 *
 * `[dependencies]` is optional; an absent one yields an empty map. A malformed
 * one is an error rather than an empty map, so a typo cannot silently drop
 * every dependency.
 */
fun Manifest.parse(s: string) -> Manifest! {
    const toml = TomlValue.parse(s)!
    // A RECORD target decodes in one step: `into` walks PackageInfo's own fields
    // and reads the table key of each name. (`PackageInfo.from(..)` is a
    // different operation -- a structural conversion, which looks for those
    // fields on the *value*; a TOML table carries them as entries, not fields.)
    const package: PackageInfo = toml.get("package")!.into()!

    let dependencies: Dependencies = HashMap.new()
    if _has(toml.keys()!, "dependencies") {
        const table = toml.get("dependencies")!
        // `keys` rejects a non-table, so `dependencies = 3` is an error here.
        for name in table.keys()! {
            dependencies.set(name, _dependency(table.get(name)!)!)
        }
    }
    return Manifest { package: package, dependencies: dependencies }
}

/**
 * Decode one `[dependencies]` entry.
 *
 * A SUM has no field list for `into` to walk -- which variant to build is a
 * decision, not a mapping -- so the entry's shape picks it explicitly.
 */
fun _dependency(entry: TomlValue) -> Dependency! {
    // `serde = "1.0"`: the bare-string shorthand for a registry version.
    match entry {
        String { value } => {
            return Dependency.Registry { version: value }
        },
        _ => {
        },
    }
    const keys = entry.keys()!
    if _has(keys, "git") {
        const rev = if _has(keys, "rev") {
            entry.get("rev")!.as_string()!
        } else {
            DEFAULT_REV
        }
        return Dependency.Git { git: entry.get("git")!.as_string()!, rev: rev }
    }
    if _has(keys, "path") {
        return Dependency.Path {
            path: Path.parse(entry.get("path")!.as_string()!),
        }
    }
    if _has(keys, "version") {
        return Dependency.Registry {
            version: entry.get("version")!.as_string()!,
        }
    }
    if _has(keys, "tarball") {
        return Dependency.Tarball {
            tarball: entry.get("tarball")!.as_string()!,
        }
    }
    return error("a dependency needs one of `version`, `git` or `path`")
}

// `TomlValue.get` reports a missing key as an error rather than null, so an
// OPTIONAL key has to be tested for before it is read.
fun _has(keys: string[], key: string) -> bool {
    for k in keys {
        if k == key {
            return true
        }
    }
    return false
}
