---
title: "Compile-time reflection"
description: "fields(x), typeof(x), definite assignment, and reflective decoders."
---

Prepoly exposes a value's type and a record's structure to code through
compile-time constructs (`fields`, `typeof`). They are resolved entirely during
type checking -- there is no runtime type information and no dynamic field
access -- so their behavior is predictable by mentally expanding them.

## `fields(x)`

`fields(x)` iterates the declared fields of `x`'s record type. It is a
compile-time construct, legal only as the iterable of a `for` loop, and the
loop is unrolled once per field in declaration order.

Inside the loop the loop variable stands for the current field. It decays to
the field's **name** as a string everywhere except the indexing form `x[field]`,
which projects the **field itself**:

```prepoly
type Point = { x: int64, y: int64 }

fun dump(p: Point) {
    for field in fields(p) {
        println("{field} = {p[field]}")   // field is a string; p[field] is the value
    }
}

dump(Point { x: 3, y: 4 })
// x = 3
// y = 4
```

Because the loop is unrolled, each iteration is ordinary typed code: `p[field]`
has the field's own type, so a type error in one iteration is reported against
that field ("while expanding field `y` of `Point`"). A type that is not a
record, using `fields` outside a `for` loop, and shadowing the loop variable in
the body are all rejected.

## `typeof(x)`

`typeof(x)` names the static type of the value `x`. It is a compile-time
construct with three uses that mirror the way `Self` names the enclosing type:

**As a string** (value position). A record or sum reports its own name (the
substitution is dropped, so the name is stable across instantiations);
primitives and structural forms (`int32[]`, `T?`, ...) report their written
form:

```prepoly
type Shape = | Circle { r: float64 } | Square
println(typeof(Shape.Circle { r: 1.0 }))      // Shape

const xs = [1, 2, 3]
println(typeof(xs))                            // int32[3]
let ys = [1, 2, 3]
println(typeof(ys))                            // int32[]
```

**As a type** (type position). `typeof(v)` denotes v's type, so a binding or
return can be declared to have the same type as another value:

```
let w: typeof(v) = ...          // w has v's type
```

**As a static receiver.** `typeof(v)` is the type of v, so a static method or
associated function of that type is reachable through a value:

```prepoly norun
const o = typeof(v).origin()    // calls the static `origin` of v's type
const n = typeof(x).from(3.9)!  // the `from` of x's numeric type
```

In every value context `typeof(v)` decays to the type's name string, exactly as
a `fields()` descriptor decays to the field name outside `v[field]`. `x` is
type-checked but never evaluated at runtime.

## Building a value field by field

An annotated `let` may omit its initializer. The binding must then be
definitely assigned before it is read -- either all at once, or, for a record,
one field at a time. A `fields` loop that stores into every field of such a
binding initializes it completely:

```prepoly
type Point = { x: int64, y: int64 }

fun doubled(p: Point) -> Point {
    let ret: Point                    // uninitialized
    for field in fields(ret) {
        ret[field] = p[field] * 2     // assigns every field across the loop
    }
    return ret                        // now fully initialized
}
```

Reading a field before it is assigned, or reading the whole binding before every
field is, is a compile error. `fields(x)` and `typeof(x)` read only the type,
so they are allowed on an uninitialized binding.

## Reflective deserialization

Together these make deserialization -- filling a struct from a name-keyed source
-- expressible without any per-type boilerplate beyond the field walk. The
target's own field names drive the lookup, and a missing key is a decode error
naming the field:

```prepoly
import std.collections.{ HashMap }

type Config = { width: int64, height: int64, depth: int64 }

fun from_map(source: HashMap) -> Config! {
    let ret: Config
    for field in fields(ret) {
        if let value = source.get(field) {
            ret[field] = value
        } else {
            return error("{typeof(ret)}: missing field '{field}'")
        }
    }
    return ret
}
```

The `if let ... else { return error(...) }` shape is understood by the
definite-assignment checker: every non-erroring path through the loop body
assigns the current field, so after the loop `ret` is fully initialized.

## Generic decoders with `-> infer!`

A method written `fun T.m(self) -> infer!` is a _reflective template_: its
result type is not fixed by the definition but by each call site's expectation.
`let u: User = j.into()!` decodes `j` as a `User`; `let n: int64 =
j.into()!` decodes the same method as an `int64`. Inside the body, `infer` is
the target type (`let ret: infer` becomes `let ret: User`), and
`infer.from(x)` converts `x` to the target when a value conversion exists
(numbers between numeric types, a value of the target's own type), producing a
runtime decode error otherwise.

This turns a whole recursive JSON-to-struct decoder into one method — this is
exactly how `std.data.json` implements `JsonValue.into` (abridged):

```prepoly norun
fun JsonValue.into(self) -> infer! {
    match self {
        JsonValue.Number { value } => { return infer.from(value) }
        JsonValue.String { value } => { return infer.from(value) }
        JsonValue.Null => { return null }
        JsonValue.Object { .. } => {
            let ret: infer                       // the target record
            for field in fields(ret) {
                ret[field] = self.get(field)!.into()!   // each field, decoded by its type
            }
            return ret
        }
    }
}

let user: User = obj.into()!                     // decodes a nested User tree
```

The compiler generates one concrete method per target type actually requested
(and, transitively, per field type a record decode needs), so there is no
runtime type dispatch: a `Json.JNum` reaching a `User` target, or a missing
field, is a normal `Result` error. The target type must be known at the call
(from an annotation or the enclosing return), not only inside a later `match`
arm.
