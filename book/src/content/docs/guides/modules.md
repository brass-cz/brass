---
title: "Modules"
description: "Splitting a program across files with imports and visibility."
---

Brass organizes code into modules: every file is a module, and directories
form the module path. The following example splits a small geometry library
across files.

First, write `geometry/vec.cz`:

```brass
type Vec2 = {
    x: float64
    y: float64
}

fun Vec2.new(x, y) {
    return Self { x: x, y: y }
}

fun Vec2.add(self, other) {
    return Self { x: self.x + other.x, y: self.y + other.y }
}

fun Vec2.length(self) {
    return sqrt(self.x * self.x + self.y * self.y)
}

fun dot(a, b) {
    return a.x * b.x + a.y * b.y
}

fun _helper() {
    // A name starting with `_` is private to this module.
}
```

Then use it from `main.cz`, next to the `geometry` directory:

```brass norun
import geometry.vec.{ Vec2, dot }

fun main() {
    let a = Vec2.new(3.0, 4.0)
    let b = Vec2.new(1.0, 2.0)
    let c = a.add(b)
    println("a + b = ({c.x}, {c.y})")
    println("a . b = {dot(a, b)}")
    println("|a|   = {a.length()}")
}
```

```bash
brass main.cz
```

```
a + b = (4.0, 6.0)
a . b = 11.0
|a|   = 5.0
```

The import path follows the directory layout relative to the importing file:
`geometry.vec` is `geometry/vec.cz`. The braced list names what to import.

Two shorter forms cover the other common needs. A single name can skip the
braces, and importing the module itself makes its exports available
qualified by the path's last segment. `as` overrides the qualifier:

```brass norun
import geometry.vec.dot     // one name, same as .{ dot }
import geometry.vec         // whole module, used as vec.<name>
import geometry.vec as g    // same, but used as g.<name>

fun main() {
    let a = vec.Vec2.new(3.0, 4.0)
    let b = vec.Vec2 { x: 1.0, y: 2.0 }
    println("a . b = {vec.dot(a, b)}")
}
```

A few points:

- A type's methods travel with it: importing `Vec2` makes `a.add(b)` and
  `Vec2.new(...)` available with no separate import.
- A name beginning with `_` (like `_helper`) is private to its module and
  cannot be imported.
- The embedded `core` library is an implicit prelude: `sqrt`, `println`,
  `HashMap`, and the array/string helpers need no import. The shipped
  `std/` tree is imported explicitly with the `std.` prefix, e.g.
  `import std.fs.{ read_file }`.

The full rules are in the [modules reference](/references/modules/).
