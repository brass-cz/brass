---
title: "Modules"
description: "Module resolution, imports, visibility, and execution order."
---

## Files are modules

One file is one module; the directory layout is the module path.
`geometry/vec.cz` is the module `geometry.vec`. There is no module
declaration inside a file.

## Imports

```brass norun
import geometry.vec.{ Vec2, dot }       // named imports (braced list)
import geometry.vec.{ dot as vdot }    // name import with rename
import geometry.vec.Vec2               // one name, same as .{ Vec2 }
import geometry.vec                    // the whole module, used qualified
import geometry.vec as g              // module import with a custom qualifier
```

Three forms:

- **`import path.{ Name, ... }`** brings the listed names into scope bare
  (trailing comma allowed). `Name as Local` renames a name on import:
  `import m.{ helper as h }` makes `h` available; `helper` is not in scope.
- **`import path.Name`** brings the one trailing name into scope, exactly
  like `import path.{ Name }`.
- **`import path`** imports the module itself. Its exports are used
  _qualified_ by the path's **last segment**: `vec.dot(a, b)`, a type
  position `vec.Vec2`, a record literal `vec.Vec2 { x: 1.0 }`, a static call
  `vec.Vec2.new(...)`, a variant literal `vec.Shape.Circle { r: 1.0 }`, and
  a match pattern `vec.Shape.Circle { r } =>` (a pattern's qualifier is
  dropped; the variant resolves against the scrutinee).
  The qualifier defaults to the last path segment; `import path as name`
  overrides it (e.g. `import geometry.vec as g` uses `g.dot(..)`). Two
  module imports whose qualifiers collide are rejected; rename one with
  `as` or import names directly.

The two brace-less forms are distinguished by what exists: if the whole path
names a module, it is a module import; otherwise the last segment is a name
imported from the module named by the rest. Qualified access disambiguates:
`import c.{ X }` and `import a.b` may coexist, with bare `X` resolving to
c's definition and `b.X` resolving to a.b's. A local binding shadows a
qualifier (`let vec = ...` makes a later `vec.x` a field access), and a
qualifier that collides with a declared or imported name is rejected.

A declaration in another module always needs an import, even when its bare name
is unique across the whole program. Program-wide uniqueness is an internal
symbol-layout detail, not implicit visibility.

Import paths are resolved according to the rules in
[Module resolution](#module-resolution). Import cycles are detected and
reported.

Importing a type brings its methods with it: `import geometry.vec.{ Vec2 }`
makes both `Vec2.new(...)` and `v.add(w)` available; methods are in scope
wherever their type is. The import also gates
[anonymous-record dispatch](/references/types/#anonymous-record-method-dispatch):
a literal like `{ x: 1.0, y: 2.0 }` only adopts a type the module declares or
imports, while a value that already carries a nominal type, an imported
function's return say, dispatches its methods without the type's name being
imported.

## Module resolution

The compiler resolves an import in this order:

1. `core.*` and bare prelude module names refer to the embedded `core`
   library. A bare spelling such as `import io` is stored as the canonical
   `core.io` module while keeping `io` as its source qualifier. These imports
   never load files from disk.
2. If the first segment is a name in `BRASS_PACKAGES`, the complete path is
   resolved only below that package root. A missing module does not fall
   through to local or include files.
3. Every other path is interpreted relative to the importing module. From
   `app/main.cz`, `import geometry.vec` first means
   `app/geometry/vec.cz`.
4. The relative path is searched below the project root, then below each
   `BRASS_INCLUDE` directory in order. A project file therefore shadows an
   include file, and an earlier include directory shadows a later one.
5. From a nested module, if the relative path does not exist, the path as
   written is also tried from those roots. This lets a file such as
   `app/features/view.cz` import a top-level `geometry` module.

`BRASS_PACKAGES` is an OS path list of `name=directory` entries. The
directory is the parent below which that package name resolves. On Unix the
entries are separated by `:`, and on Windows by `;`:

```text
BRASS_PACKAGES=geometry=/opt/geometry:std=/opt/brass
```

`BRASS_INCLUDE` is an OS path list of open module roots:

```text
BRASS_INCLUDE=/opt/brass-extras:/home/user/brass-modules
```

Avoid overlapping include roots: the same source can otherwise be loaded
under two module paths. Package bindings take precedence over all local and
include paths, so a declared dependency cannot be shadowed accidentally.

A distributed toolchain supplies an implicit `std` package rooted beside its
`bin/` directory. An explicit `std=...` entry in `BRASS_PACKAGES` overrides
it. Repository builds do not have this installed layout; use the packaged
toolchain or provide `std` explicitly.

## Visibility

A name is public unless it starts with `_`:

- a `_`-prefixed function, type, or global is private to its module and
  cannot be imported;
- a `_`-prefixed _module_ (file or last path segment) cannot be imported at
  all.

There is no other visibility control.

## `_PATH`

Every module is loaded with a constant naming its own source file:

```brass norun
println(_PATH)          // /home/you/project/src/main.cz
```

The path is absolute, so it does not depend on where the program was started.
`_PATH` follows the visibility rule above: its leading `_` makes it private,
so a module always reads its own, never an importer's, and no module can export
one. A module with no file on disk (an embedded `core` module, a plugin's
synthesized wrapper) reads its diagnostic label instead, such as `<core/io>`.

To take the path apart, hand it to [`std.path`](/references/stdlib/#stdpath):
`Path.parse(_PATH).parent()` is the directory holding the file you are writing.

## The standard library

The embedded `core/` modules (`io`, `array`, `string`, `math`, `conv`,
`assert`, `error`, `is`, `default`, `collections`) form the **implicit
prelude**: their public names are in scope everywhere without an import,
`HashMap` included. They can also be imported explicitly by their bare name
(`import io.{ ... }`) or `core` path (`import core.io.{ ... }`), to alias or
qualify a name.

The shipped `std/` tree (`fs`, `net`, `process`, `data.json`, ...) is not
embedded. It resolves as the package named `std`, which an installed
toolchain binds automatically, and imports with the `std.` prefix
(`import std.fs.{ read_file }`). See the
[standard library reference](/references/stdlib/).

## Execution order

Each module's top-level statements are gathered into a module initializer.
Initializers run first, in dependency order, then `main` is called if the
program defines one. Within a module, globals initialize in textual order, and
using a global before its initializer has run is a compile error.
