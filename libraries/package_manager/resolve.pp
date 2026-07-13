import std.collections.HashMap
import process.{ Command }
import path.Path
import env.var
import fs.{ read_file, create_dir }

import manifest.{ Manifest, Dependency, Dependencies }

const PACKAGE_FILE_NAME = "package.toml"

fun resolve_deps(deps: Dependencies) {
    let result = HashMap.new()
    for [key, val] in deps.pairs() {
        const path = match val {
            Git { git, rev } => {
                git_clone(git, rev)!
            },
            Path { path } => {
                path
            },
            _ => {
                return error("not supported deps yet!")
            },
        }
        const manifest = Manifest.parse(
            read_file(path.join(PACKAGE_FILE_NAME).to_string())!,
        )!
        const name = manifest.package.name
        result.set(name, path.to_string())
        for [key, val] in resolve_deps(manifest.dependencies)!.pairs() {
            result.set(key, val)
        }
    }
    return result
}

fun git_clone(repo: string, rev: string) {
    const pkgs = Path
        .parse(var("HOME")!)
        .join(".prepoly")
        .join("packages")
        .join("git")
    const repo = repo.replace("/", "-").replace(":", "-")
    const path = pkgs.join(repo).join(rev)
    if path.is_dir() {
        return path
    }
    if !pkgs.is_dir() {
        create_dir(pkgs)!
    }

    let cmd = Command.new("git")
    cmd.args(["clone", repo, path.to_string()])
    const child = cmd.spawn()!
    const code = child.wait()!
    if code != 0 {
        return error("failed to clone: exit code {code}")
    }
    let cmd = Command.new("git")
    cmd.args(["checkout", rev])
    const child = cmd.spawn()!
    const code = child.wait()!
    if code != 0 {
        return error("failed to clone: exit code {code}")
    }
    return path
}
