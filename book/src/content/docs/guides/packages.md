---
title: "Package manager"
description: "Creating projects and managing dependencies with ppm."
---

prepoly ships a minimal package manager called **ppm** (prepoly package
manager). It handles project scaffolding, dependency fetching, and
compilation/execution with a handful of commands.

## Creating a project

`ppm new` creates a new directory and scaffolds a project inside it:

```bash
ppm new myapp
```

This creates a new directory with the following layout:

| Path                | Purpose                                                                      |
| ------------------- | ---------------------------------------------------------------------------- |
| `myapp/myapp/`      | Source directory for sub-modules                                             |
| `myapp/myapp.pp`    | Package root file (your program's entry point)                               |
| `myapp/package.toml`| Package manifest                                                             |
| `myapp/AGENTS.md`   | Instructions teaching LLM agents prepoly (see [LLM agents](/guides/llm/))    |
| `myapp/CLAUDE.md`   | Symlink to `AGENTS.md`, so Claude Code reads the same instructions           |

To initialize a project in the current directory instead, use `ppm init`:

```bash
mkdir myapp && cd myapp
ppm init myapp
```

The generated `package.toml` looks like this:

```toml
[package]
name = "myapp"
author = ""
license = "MIT"

[dependencies]
# mylib = { git = "https://github.com/user/mylib", hash = "<commit hash>" }
# mylib = { path = "../mylib" }
```

The commented lines show the two dependency forms, ready to fill in.

## Running and checking

Inside a project directory (where `package.toml` lives), use:

```bash
ppm run      # compile and run
ppm check    # type-check only
```

Both commands read `package.toml`, fetch any missing dependencies, set the
`PREPOLY_PACKAGES` environment variable, and invoke `prepoly` on the root
file (`<package-name>.pp`).

## The language server in a project

`ppm lsp` starts `ppls` with the same dependency resolution, so editor
diagnostics, hover, and completion see the project's dependencies. Point your
editor's LSP command at `ppm lsp` instead of `ppls` (see
[Installing the LSP server](/installation/lsp/)). In a directory without a
`package.toml` it simply starts the plain server, so the one editor
configuration works for projects and loose `.pp` files alike.

## Adding dependencies

A dependency is either a Git repository pinned to a commit hash, or a local
directory given by path. Add them to the `[dependencies]` section of
`package.toml`:

```toml
[dependencies]
"geometry" = { git = "https://github.com/user/geometry-pp", hash = "a1b2c3d4e5f6" }
"utils"    = { git = "https://github.com/user/utils-pp",    hash = "deadbeef1234" }
"mylib"    = { path = "../mylib" }
```

When you run `ppm run` or `ppm check`, each Git dependency is cloned to
`~/.prepoly/packages/<name>-git-<hash>` if it is not already present, and
then checked out at the pinned commit.

A `path` dependency is used in place — nothing is copied or fetched. The
path is resolved relative to the project root (the directory holding
`package.toml`) and must point at the dependency project's root directory:
the one containing its `<package-name>.pp` root file. Edits to the
dependency are picked up on the next `ppm run`/`ppm check` with no extra
step, which makes `path` the form to use while developing a library
alongside its consumer; a dependency cannot combine `path` with
`git`/`hash`.

## Importing from a dependency

Once a dependency is declared, its modules are available via `import`:

```prepoly norun
// Import specific names from the package root
import geometry.{ Vec2, dot }

// Import a sub-module
import geometry.utils.{ normalize }

// Qualified module import
import geometry
// then use: geometry.Vec2, geometry.dot(...)
```

The package root file is `<package-name>.pp` inside the dependency directory,
and sub-modules live under the `<package-name>/` directory — the same
layout that `ppm new` creates.

## Writing a library package

A library package has the same layout as an application. Declare the public
API in the root file and organize implementation details into sub-modules.
Names starting with `_` are private and cannot be imported by dependents (see
[Modules](/guides/modules/)).

```
mylib/
  mylib.pp            # public API: types, functions
  mylib/
    _internal.pp      # private helper (not importable)
    extra.pp          # public sub-module
  package.toml
```

## How it works

`ppm` sets the environment variable `PREPOLY_PACKAGES` before invoking
`prepoly`. The format is a colon-separated list of `name=path` entries:

```
PREPOLY_PACKAGES=geometry=/home/user/.prepoly/packages/geometry-git-a1b2c3d4:utils=/home/user/.prepoly/packages/utils-git-deadbeef
```

An import whose first segment is a declared name resolves under that entry's
directory — and only there. The manifest therefore scopes exactly which
external modules the project sees, and a declared name cannot be shadowed by
a same-named local file. `ppm` warns when a dependency directory contains no
module of the declared name (the misnamed entry would otherwise only fail at
its first import). Both the compiler and the language server read the
variable at startup, so editor diagnostics and completions work for
dependencies too.

## Include paths

Outside of `ppm` projects — or alongside them — the compiler also honors
`PREPOLY_INCLUDE`, a colon-separated list of plain directories:

```
PREPOLY_INCLUDE=/opt/prepoly/libraries:/home/user/pp-modules
```

Any `.pp` file, module directory, or plugin under an include path is
importable directly, no manifest required. An import is resolved relative to
the importing file first, searched across the project root and then each
include path in list order; the first directory that serves the path wins. A
file in the project therefore shadows an include module of the same path, an
earlier include entry shadows a later one, and a `PREPOLY_PACKAGES` name
always binds before the include search. Include entries should not nest
inside each other (or inside the project): a file reachable from two roots
can be loaded twice under two module paths.

Finally, the toolchain binaries (`prepoly` and `ppls`) append one
implicit include entry: the `libraries/` directory sitting beside their own
`bin/` directory (`<bin>/../libraries`), when it exists. A distributed
toolchain therefore serves its bundled libraries (`process`, `path`, ...)
with no environment setup at all — in the compiler and in the editor alike —
and explicit include paths and package declarations always take precedence
over it.
