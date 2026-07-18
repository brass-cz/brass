---
title: "Package manager"
description: "Creating projects and managing dependencies with czpm."
---

Brass ships a minimal package manager called **czpm** (Brass package
manager). It handles project scaffolding, dependency fetching, and
compilation/execution with a handful of commands.

## Creating a project

`czpm new` creates a new directory and scaffolds a project inside it:

```bash
czpm new myapp
```

This creates a new directory with the following layout:

| Path                 | Purpose                                        |
| -------------------- | ---------------------------------------------- |
| `myapp/myapp/`       | Source directory for sub-modules               |
| `myapp/myapp.cz`     | Package root file (your program's entry point) |
| `myapp/package.toml` | Package manifest                               |

To initialize a project in the current directory instead, use `czpm init`:

```bash
mkdir myapp && cd myapp
czpm init myapp
```

Package and dependency names must be ASCII identifiers: they begin with a
letter or `_` and continue with letters, digits, or `_`. `new` refuses an
existing destination directory, while `init` refuses to overwrite an existing
`package.toml` or package root file.

The generated `package.toml` looks like this:

```toml
[package]
name = "myapp"
author = ""
license = "MIT"

[dependencies]
# mylib = { git = "https://github.com/user/mylib", rev = "<rev>" }
# mylib = { path = "../mylib" }
```

The commented lines show the two dependency forms, ready to fill in.

## Running and checking

Inside a project directory (where `package.toml` lives), use:

```bash
czpm run      # compile and run
czpm check    # type-check only
czpm fmt      # format every owned .cz file below the project directory
```

Both commands read `package.toml`, fetch any missing dependencies, set the
`BRASS_PACKAGES` environment variable, and invoke `brass` on the root
file (`<package-name>.cz`).

## The language server in a project

`czpm lsp` starts `czls` with the same dependency resolution, so editor
diagnostics, hover, and completion see the project's dependencies. Point your
editor's LSP command at `czpm lsp` instead of `czls` (see
[Installing the LSP server](/installation/lsp/)). In a directory without a
`package.toml` it simply starts the plain server, so the one editor
configuration works for projects and loose `.cz` files alike.

## Adding dependencies

A dependency is either a Git repository at a revision, or a local directory
given by path. Add them to the `[dependencies]` section of `package.toml`:

```toml
[dependencies]
geometry = { git = "https://github.com/user/geometry-pp", rev = "a1b2c3d4e5f6" }
utils    = { git = "https://github.com/user/utils-pp",    rev = "deadbeef1234" }
mylib    = { path = "../mylib" }
```

When you run `czpm run` or `czpm check`, each Git dependency is cloned to
`~/.brass/packages/git/<digest>` if it is not already present, and then checked
out at `rev`. The digest identifies the repository URL and revision without
putting either one directly in a path. `rev` may name any revision Git accepts;
when omitted it defaults to `HEAD`, though an immutable commit is recommended
for repeatable builds.

A `path` dependency is used in place: nothing is copied or fetched. The
path is resolved relative to the `package.toml` that declares it, including for
transitive dependencies, and must point at the dependency project's root
directory. Edits to the dependency are picked up on the next `czpm run`/`czpm
check` with no extra step, which makes `path` the form to use while developing a
library alongside its consumer; a dependency cannot combine `path` with `git`
or `rev`.

## Importing from a dependency

Once a dependency is declared, its modules are available via `import`:

```brass norun
// Import specific names from the package root
import geometry.{ Vec2, dot }

// Import a sub-module
import geometry.utils.{ normalize }

// Qualified module import
import geometry
// then use: geometry.Vec2, geometry.dot(...)
```

The package root file is `<package-name>.cz` inside the dependency directory,
and sub-modules live under the `<package-name>/` directory: the same
layout that `czpm new` creates.

## Writing a library package

A library package has the same layout as an application. Declare the public
API in the root file and organize implementation details into sub-modules.
Names starting with `_` are private and cannot be imported by dependents (see
[Modules](/guides/modules/)).

```
mylib/
  mylib.cz            # public API: types, functions
  mylib/
    _internal.cz      # private helper (not importable)
    extra.cz          # public sub-module
  package.toml
```

## How it works

`czpm` sets the environment variable `BRASS_PACKAGES` before invoking `brass`.
It is an OS path list of `name=path` entries: entries are separated by `:` on
Unix and `;` on Windows. For example, on Unix:

```
BRASS_PACKAGES=geometry=/home/user/.brass/packages/git/0123abcd:utils=/home/user/.brass/packages/git/4567cdef
```

An import whose first segment is a declared name resolves under that entry's
directory, and only there. The manifest therefore scopes exactly which
external modules the project sees, and a declared name cannot be shadowed by a
same-named local file. Resolution rejects a dependency whose manifest package
name differs from its dependency-table key, as well as two transitive
dependencies that give the same name different locations. Both the compiler
and the language server read the variable at startup, so editor diagnostics and
completions work for dependencies too.

The **standard library is itself the package named `std`**: an entry
`std=/path/to/toolchain` (the directory containing `std/`) is what makes
`import std.fs` resolve. A distributed toolchain binds it implicitly (see
below), and `czpm` passes the parent process's `BRASS_PACKAGES` on to the
compiler it spawns with the manifest's dependencies appended, so the `std`
binding survives inside a project while a manifest-declared name still wins
on a collision.

## Include paths

Outside of `czpm` projects (or alongside them), the compiler also honors
`BRASS_INCLUDE`, an OS path list of plain directories. This Unix example uses
`:`; use `;` on Windows:

```
BRASS_INCLUDE=/opt/brass-extras:/home/user/brass-modules
```

Any `.cz` file, module directory, or plugin under an include path is
importable directly, no manifest required. An import is resolved relative to
the importing file first, searched across the project root and then each
include path in list order; the first directory that serves the path wins. A
file in the project therefore shadows an include module of the same path, an
earlier include entry shadows a later one, and a `BRASS_PACKAGES` name
always binds before the include search. Include entries should not nest
inside each other (or inside the project): a file reachable from two roots
can be loaded twice under two module paths.

Finally, the toolchain binaries (`brass` and `czls`) bind one implicit
package: `std`, rooted at the directory beside their own `bin/`
(`<bin>/..`) when `std/` exists there. A distributed toolchain therefore
serves the standard library (`import std.process`, `import std.path`, ...)
with no environment setup at all, in the compiler and in the editor alike.
An explicit `std=...` entry in `BRASS_PACKAGES` takes precedence over the
implicit binding, so an environment can point the standard library
elsewhere.
