# Modules

prepoly organizes code into modules: every file is a module, and directories
form the module path. Let's split a small geometry library across files.

First, write `geometry/vec.pp`:

```prepoly
type Vec2 = {
    x: float64
    y: float64
}

fun Vec2.new(x: float64, y: float64) {
    return Self { x: x, y: y }
}

fun Vec2.add(self, other: Vec2) -> Vec2 {
    return Self { x: self.x + other.x, y: self.y + other.y }
}

fun Vec2.length(self) -> float64 {
    return sqrt(self.x * self.x + self.y * self.y)
}

fun dot(a: Vec2, b: Vec2) -> float64 {
    return a.x * b.x + a.y * b.y
}

fun _helper() {
    // A name starting with `_` is private to this module.
}
```

Then use it from `main.pp`, next to the `geometry` directory:

```prepoly
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
prepoly main.pp
```

```
a + b = (4.0, 6.0)
a . b = 11.0
|a|   = 5.0
```

The import path follows the directory layout relative to the importing file:
`geometry.vec` is `geometry/vec.pp`. The braced list names what to import.

A few points worth noting:

- A type's methods travel with it: importing `Vec2` makes `a.add(b)` and
  `Vec2.new(...)` available with no separate import.
- A name beginning with `_` (like `_helper`) is private to its module and
  cannot be imported.
- The top-level standard library is an implicit prelude — `sqrt`, `println`,
  and the array/string helpers need no import. Nested standard-library
  modules are not in the prelude and are imported explicitly, e.g.
  `import std.collections.hashmap.{ HashMap }`.

The full rules are in the [modules reference](references/modules.md).
