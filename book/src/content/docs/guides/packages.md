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

The name passed to `new` or `init` begins with an ASCII letter or `_` and may
continue with letters, digits, `_`, or internal `-` characters. A name cannot
end in `-`; hyphens become underscores in the generated source file and module
directory. Dependency keys are ASCII identifiers without hyphens because they
become import names. `new` refuses an existing destination directory, while
`init` refuses to overwrite an existing `package.toml` or package root file.

The generated `package.toml` looks like this:

```toml
[package]
name = "myapp"
authors = ""
license = "MIT"

[dependencies]
# mylib = { git = "https://github.com/user/mylib", rev = "<rev>" }
# mylib = { path = "../mylib" }
# mylib = { tarball = "https://example.com/mylib.tar.gz", hash = "<sha256>" }
```

The commented lines show the three dependency forms, ready to fill in.
`authors` accepts either one string or an array of strings.

## Running and checking

Inside a project directory (where `package.toml` lives), use:

```bash
czpm run      # compile and run
czpm check    # type-check only
czpm fmt      # format every owned .cz file below the project directory
```

All three commands read `package.toml` and resolve its dependencies. `run`
invokes `brass` on the package root (with any name hyphens replaced by
underscores); `check` checks every owned `.cz` file so errors in unused modules
are reported too; `fmt` formats those files in place.

## The language server in a project

`czpm lsp` starts `czls` with the same dependency resolution, so editor
diagnostics, hover, and completion see the project's dependencies. Point your
editor's LSP command at `czpm lsp` instead of `czls` (see
[Installing the LSP server](/installation/lsp/)). In a directory without a
`package.toml` it simply starts the plain server, so the one editor
configuration works for projects and loose `.cz` files alike.

## Adding dependencies

A dependency is a Git repository at a revision, a local directory given by
path, or a tarball pinned by its SHA-256 digest. Add it to the `[dependencies]`
section of `package.toml`:

```toml
[dependencies]
geometry = { git = "https://github.com/user/geometry-pp", rev = "a1b2c3d4e5f6" }
utils    = { git = "https://github.com/user/utils-pp",    rev = "deadbeef1234" }
mylib    = { path = "../mylib" }
archive  = { tarball = "https://example.com/archive.tar.gz", hash = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef" }
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

A `tarball` dependency requires a 64-character lowercase hexadecimal SHA-256
`hash`. `czpm` verifies the downloaded bytes before extracting the archive and
caches a completed extraction under `~/.brass/packages/tarball/<hash>`. A
dependency entry cannot mix `tarball`/`hash` with the Git or path fields.

## Managing cached packages

```bash
czpm cache info
czpm cache clean
czpm cache clean geometry utils
```

These commands manage `$HOME/.brass/packages` without network access. They
leave the JIT object cache alone; use `brass cache` for that store.

`info` lists Git checkouts and tarball extractions with their sizes and totals.
It reports stale staging directories separately. Inside a package, entries
known to the local dependency graph also show their dependency names and
sources. Other entries show their digest. Sizes count regular-file bytes;
links are not followed. A missing store is empty.

`clean` removes all digest-named package directories and stale staging trees.
Unknown names, symbolic links, and fresh staging trees stay intact. A staging
tree is stale only after 24 hours without a modification anywhere inside it.
The store root and its `git` and `tarball` directories are preserved.

`clean NAME...` requires `package.toml` in the current directory. Direct names
come from that manifest. Transitive names come from manifests already present
in cached packages or local path dependencies. Paths are relative to the
manifest that declares them. Missing or unreadable child manifests end that
branch; no clone, download, or revision lookup occurs. Cycles are visited once.
Path dependencies have nothing cached and are reported without removal.

Every requested name must resolve before deletion starts. An unknown, missing,
or ambiguous dependency is an error that names it; nothing is deleted. Repeated
names and shared entries are removed once. Named cleanup removes published
entries only. A filesystem error during removal can leave a partial cleanup.
Concurrent fetches may repopulate the store.

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

The package root file and sub-module directory use the package name with
hyphens replaced by underscores: for package `my-lib`, they are `my_lib.cz`
and `my_lib/`. This is the same layout that `czpm new` creates.

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

## Dependency resolution

`czpm` passes the resolved dependency roots to `brass` and `czls`, so imports,
editor diagnostics, and completion all use the same packages. It also keeps
the installed `std` package available. You normally do not need to configure
the environment yourself.

For the exact `BRASS_PACKAGES` format, `BRASS_INCLUDE`, precedence, and the
implicit `std` binding, see
[Module resolution](/references/modules/#module-resolution).
