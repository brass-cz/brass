---
title: "Modules"
description: "Module resolution, imports, visibility, and execution order."
---

## Files are modules

One file is one module; the directory layout is the module path.
`geometry/vec.pp` is the module `geometry.vec`. There is no module
declaration inside a file.

## Imports

```prepoly norun
import geometry.vec.{ Vec2, dot }
```

`import path.{ Name, ... }` is the only form: a dotted module path followed by
a braced list of the names to import (trailing comma allowed). There is no
bare `import path` form and no renaming (`as`).

Import paths resolve **relative to the importing file's directory**: inside
`app/main.pp`, `import geometry.vec.{...}` refers to `app/geometry/vec.pp`.
Paths starting with `std` are global and refer to the embedded standard
library instead of files on disk. Import cycles are detected and reported.

Importing a type brings its methods with it — `import geometry.vec.{ Vec2 }`
makes both `Vec2.new(...)` and `v.add(w)` available; methods are in scope
wherever their type is.

## Visibility

A name is public unless it starts with `_`:

- a `_`-prefixed function, type, or global is private to its module and
  cannot be imported;
- a `_`-prefixed _module_ (file or last path segment) cannot be imported at
  all.

There is no other visibility control.

## The standard library

The top-level `std` modules (`io`, `array`, `string`, `math`, `conv`,
`assert`) form the **implicit prelude**: their public names are in scope
everywhere without an import. They can also be imported explicitly by their
bare name (`import io.{ ... }`) or `std` path.

Nested standard-library modules — `std.collections.hashmap`,
`std.data.json` — are **not** in the prelude. They are embedded in the
compiler but loaded only when a module imports them (transitively: a nested
std module may import another). See the
[standard library reference](/references/stdlib/).

## Execution order

Each module's top-level statements are gathered into a module initializer.
Initializers run first, in dependency order, then `main` is called if the
program defines one. Within a module, globals initialize in textual order, and
using a global before its initializer has run is a compile error.
