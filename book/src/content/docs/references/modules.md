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

Import paths resolve **relative to the importing file's directory**: inside
`app/main.cz`, `import geometry.vec.{...}` refers to `app/geometry/vec.cz`.
Paths starting with `std` are global and refer to the embedded standard
library instead of files on disk. Import cycles are detected and reported.

Importing a type brings its methods with it: `import geometry.vec.{ Vec2 }`
makes both `Vec2.new(...)` and `v.add(w)` available; methods are in scope
wherever their type is. The import also gates
[anonymous-record dispatch](/references/types/#anonymous-record-method-dispatch):
a literal like `{ x: 1.0, y: 2.0 }` only adopts a type the module declares or
imports, while a value that already carries a nominal type, an imported
function's return say, dispatches its methods without the type's name being
imported.

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

The shipped `std/` tree (`fs`, `net`, `process`, `data.json`, ...) is NOT
embedded: it resolves as the package named `std`, which a distributed
toolchain binds automatically, and imports with the `std.` prefix
(`import std.fs.{ read_file }`). See the
[standard library reference](/references/stdlib/).

## Execution order

Each module's top-level statements are gathered into a module initializer.
Initializers run first, in dependency order, then `main` is called if the
program defines one. Within a module, globals initialize in textual order, and
using a global before its initializer has run is a compile error.
