---
title: "Reflection"
description: "Compile-time field iteration with fields(x) and type naming with typeof(x)."
---

prepoly can walk a record's fields at _compile time_: no runtime type
information is involved, and everything stays fully type-checked.

## Walking fields

`fields(x)` iterates the declared fields of `x`'s record type inside a `for`
loop. The loop variable is the field **name** (a string) — except in the
indexing form `x[field]`, which projects the field's **value**:

```prepoly
type Point = { x: int64, y: int64 }

fun dump(p: Point) {
    for field in fields(p) {
        println("{field} = {p[field]}")
    }
}

dump(Point { x: 3, y: 4 })
```

The loop is unrolled once per field during type checking, so each iteration is
ordinary typed code.

## Building a value field by field

An annotated `let` may omit its initializer; the compiler then checks the
binding is definitely assigned before use. Combined with a `fields` loop, this
builds a record without naming its fields:

```prepoly
type Point = { x: int64, y: int64 }

fun doubled(p: Point) -> Point {
    let ret: Point                    // uninitialized
    for field in fields(ret) {
        ret[field] = p[field] * 2     // assigns every field
    }
    return ret                        // now fully initialized
}

println(doubled(Point { x: 3, y: 4 }))
```

Because `doubled` never names `x` or `y`, it keeps working when `Point` gains
a field.

## Naming a type with `typeof`

`typeof(x)` names the static type of `x`. It is a string in value position, a
type in type position, and a static receiver for method calls:

```prepoly
fun main() {
    let xs = [1, 2, 3]
    println(typeof(xs))            // int32[] — a growable array
    const ys = [1, 2, 3]
    println(typeof(ys))            // int32[3] — const binds a fixed-length array

    let n = 1
    let m: typeof(n) = 2           // m has n's type
    let k = typeof(n).from(3.9)!   // int32.from — k is 3
    println("{m} {k}")
}
```

These pieces combine into reflective _deserialization_ — filling a struct from
name-keyed data, or a whole JSON-to-struct decoder written once as
`fun Json.into(self) -> infer!`. See the
[reflection reference](/references/reflection/) for the complete rules and
the decoder pattern.
