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

fun doubled(p: Point) {
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
let xs = [1, 2, 3]
println(typeof(xs))            // int32[] — a growable array
const ys = [1, 2, 3]
println(typeof(ys))            // int32[3] — const binds a fixed-length array

let n = 1
let m: typeof(n) = 2           // m has n's type
let k = typeof(n).from(3.9)!   // int32.from — k is 3
println("{m} {k}")
```

These pieces combine into reflective _deserialization_ — filling a struct from
name-keyed data, or a whole JSON-to-struct decoder written once as
`fun Json.into(self) -> infer!`. See the
[reflection reference](/references/reflection/) for the complete rules and
the decoder pattern.

## Dispatching on a value's type

An **uncalled** member access asks, at compile time, whether the value's type
has that member: present reads truthy, absent reads `null`. Because only the
arm that fits ever gets checked or compiled, one generic function can accept
several unrelated types and treat each its own way.

Two kinds of members make this a type dispatch. Each primitive type
implements only its own `is_<type>` method (`is_string`, `is_int32`,
`is_bool`, `is_array`, ...), so `v.is_string` answers "is this a string?".
And a declared method (`fun T.m`) reads as present exactly on its type, so
`if v.m { v.m() }` dispatches on whether the receiver implements `m`:

```prepoly
type Point = { x: int32, y: int32 }

fun Point.norm2(self) -> int32 {
    return self.x * self.x + self.y * self.y
}

fun describe(v) -> string {
    if v.is_string {
        return "string of {v.len()} bytes"
    } else if v.is_int32 {
        return "int32 {v}"
    } else if v.norm2 {
        return "point with norm^2 {v.norm2()}"
    }
    return "something else"
}

println(describe("hello"))
println(describe(42))
println(describe(Point { x: 3, y: 4 }))
println(describe(1.5))
```

Each call compiles only its own arm: `describe("hello")` never type-checks
`v.norm2()` against `string`. The
[reference](/references/reflection/#member-presence-xm-without-a-call) has
the full rules, including how record fields participate.
