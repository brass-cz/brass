import std.collections.HashMap
import env
import fs.{ create_dir, read_file, write_file }
import path.Path
import process.{ Command, exit }

import manifest.Manifest
import resolve.{ PACKAGE_FILE_NAME, resolve_deps }

fun main() {
    const stderr = File.stderr()
    const current = env.current_dir()!

    const args = env.args()
    if args.len() < 2 {
        help()
    }
    const cmd = args[1]
    if cmd == "new" {
        if args.len() < 3 {
            help()
        }

        const name = args[2]
        const path = current.join(name)
        create_dir(path)!
        init_dir(path, name)!
    } else if cmd == "init" {
        if args.len() < 3 {
            help()
        }
        init_dir(current, args[2])!
    }

    const manifest = if let Ok { value } = read_file(
        current.join(PACKAGE_FILE_NAME),
    ) {
        if let Ok { value } = Manifest.parse(value) {
            value
        } else {
            error("failed to parse manifest file {PACKAGE_FILE_NAME}")!
        }
    } else {
        if cmd == "lsp" {
            const code = run_ppls("")!
            exit(code)
        }
        error("failed to read package manifest file {PACKAGE_FILE_NAME}")!
    }
    const name = manifest.package.name
    const main_path = if Path.parse(name).is_file() {
        Path.parse(name)
    } else if Path.parse("{name}.pp").is_file() {
        Path.parse("{name}.pp")
    } else {
        return error("failed to find {name}: {name} or {name}.pp not found")
    }
    const files = list_files(Path.parse("."))!.filter(
        (v) -> v.to_string().ends_with(".pp"),
    )

    if cmd == "fmt" {
        for path in files {
            const code = run_cmd("ppfmt", ["--write", path.to_string()], "")!
            if code != 0 {
                println("FAIL: {path.to_string()}")
                exit(code)
            } else {
                println("OK: {path.to_string()}")
            }
        }
        exit(0)
    }

    const deps = join_deps(resolve_deps(manifest.dependencies)!)

    if cmd == "run" {
        exit(run_prepoly([main_path.to_string()], deps)!)
    } else if cmd == "check" {
        let fail = false
        for path in files {
            const code = run_prepoly(["check", path.to_string()], deps)!
            if code != 0 {
                fail = true
                println("FAIL: {path.to_string()}")
            } else {
                println("OK: {path.to_string()}")
            }
        }
        if fail {
            println("FAIL")
            exit(1)
        } else {
            println("ALL PASSED")
            exit(0)
        }
    } else if cmd == "lsp" {
        const code = run_ppls(deps)!
        exit(code)
    }
    help()
}

fun join_deps(deps: HashMap) {
    let env = []
    for [key, val] in deps.pairs() {
        env.push("{key}={val}")
    }
    return env.join(":")
}

fun help() {
    println(
        "ppm - prepoly Package Manager

Usage:
    ppm new [name]  -> Create a new prepoly package in a new directory
    ppm init [name] -> Initialize a prepoly package in the current directory
    ppm run         -> Run the current package
    ppm check       -> Type-check the current package
    ppm fmt         -> Format all prepoly files
    ppm lsp         -> Start the Language Server (ppls)
",
    )
    exit(1)
}

fun init_dir(path: Path, name: string) {
    if !path.is_dir() {
        create_dir(path)!
    }

    // write package.toml
    write_file(
        path.join("package.toml"),
        "[package]
name = \"{name}\"
author = \"\"
license = \"MIT\"

[dependencies]
# mylib = \{ git = \"https://github.com/user/mylib\", rev = \"<rev>\" \}
# mylib = \{ path = \"../mylib\" \}",
    )!

    // write [name].pp
    write_file(path.join("{name}.pp"), "println(\"Hello, {name}!\")")!

    // create [name] dir but replaced
    create_dir(path.join(name.replace("-", "_")))!

    println("Package {name} created at {path.to_string()}!")
    exit(0)
}

fun list_files(dir: Path) {
    let result = []
    for entry in dir.entries()! {
        const components = entry
            .components()
            .filter((v) -> v != "." && v != "..")
        if components.len() == 0 {
            continue
        }
        let path = Path.parse(components[0])
        for component in components.slice(1, components.len()) {
            path = path.join(component)
        }
        if path.is_dir() {
            for path in list_files(path)! {
                result.push(path)
            }
        } else {
            result.push(path)
        }
    }
    return result
}

fun run_prepoly(args: string[], deps: string) {
    return run_cmd("prepoly", args, deps)
}

fun run_ppls(deps: string) {
    return run_cmd("ppls", [], deps)
}

fun run_cmd(command: string, args: string[], deps: string) {
    let cmd = Command.new(command)
    cmd.args(args)
    cmd.env("PREPOLY_PACKAGES", deps)
    const child = cmd.spawn()!
    return child.wait()
}
