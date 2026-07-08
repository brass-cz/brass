---
title: "Package manager"
description: "Creating projects and managing dependencies with ppm."
---

prepoly ships a minimal package manager called **ppm** (prepoly package
manager). It handles project scaffolding, dependency fetching, and
compilation/execution with a handful of commands.

## Creating a project

`ppm new` scaffolds a new project:

```bash
ppm new myapp
```

This creates three things in the current directory:

| Path           | Purpose                                        |
| -------------- | ---------------------------------------------- |
| `myapp/`       | Source directory for sub-modules               |
| `myapp.pp`     | Package root file (your program's entry point) |
| `package.toml` | Package manifest                               |

The generated `package.toml` looks like this:

```toml
[package]
name = "myapp"
author = ""
license = "MIT"

[dependencies]
```

## Running and checking

Inside a project directory (where `package.toml` lives), use:

```bash
ppm run      # compile and run
ppm check    # type-check only
```

Both commands read `package.toml`, fetch any missing dependencies, set the
`PREPOLY_PACKAGES` environment variable, and invoke `prepoly` on the root
file (`<package-name>.pp`).

## Adding dependencies

Dependencies are Git repositories pinned to a commit hash. Add them to the
`[dependencies]` section of `package.toml`:

```toml
[dependencies]
"geometry" = { git = "https://github.com/user/geometry-pp", hash = "a1b2c3d4e5f6" }
"utils"    = { git = "https://github.com/user/utils-pp",    hash = "deadbeef1234" }
```

When you run `ppm run` or `ppm check`, each dependency is cloned to
`~/.prepoly/packages/<name>-git-<hash>` if it is not already present, and
then checked out at the pinned commit.

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

Both the compiler and the language server read this variable at startup, so
editor diagnostics and completions work for dependencies too.
