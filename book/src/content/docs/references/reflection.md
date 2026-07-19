---
title: "Compile-time reflection"
description: "fields(x), typeof(x), definite assignment, and reflective decoders."
---

Brass exposes a value's type and a record's structure to code through
compile-time constructs (`fields`, `typeof`). They are resolved entirely during
type checking: there is no runtime type information and no dynamic field
access, so their behavior is predictable by mentally expanding them.

## `fields(x)`

`fields(x)` iterates the declared fields of `x`'s record type. It is a
compile-time construct, legal only as the iterable of a `for` loop, and the
loop is unrolled once per field in declaration order.

Inside the loop the loop variable stands for the current field. It decays to
the field's **name** as a string everywhere except the indexing form `x[field]`,
which projects the **field itself**:

```brass
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
form. The name is resolved per monomorphic instance, so a generic function
reports each caller's own argument type:

```brass
type Shape = | Circle { r: float64 } | Square
println(typeof(Shape.Circle { r: 1.0 }))      // Shape

let xs = [1, 2, 3]
println(typeof(xs))                            // int32[]

fun name(x) -> string { return typeof(x) }
println(name(1))                               // int32
println(name("s"))                             // string
```

**As a type** (type position). `typeof(v)` denotes v's type, so a binding or
return can be declared to have the same type as another value:

```
let w: typeof(v) = ...          // w has v's type
```

**As a static receiver.** `typeof(v)` is the type of v, so a static method or
associated function of that type is reachable through a value:

```brass norun
const o = typeof(v).origin()    // calls the static `origin` of v's type
const n = typeof(x).from(3.9)!  // the `from` of x's numeric type
```

In every value context `typeof(v)` decays to the type's name string, exactly as
a `fields()` descriptor decays to the field name outside `v[field]`. Only the
operand's type is consulted, so a bare variable costs nothing at runtime; a
compound operand (a call, an element read) is still evaluated for its effects,
like any other argument.

## Member presence: `x.m` without a call

An _uncalled_ member access asks whether `x`'s type has a member `m`, and the
answer is fixed at compile time:

- a **field** reads as the field's value, as always;
- a **method** decays to its own **name** as a string, exactly as a `fields()`
  descriptor does: a non-null value, so it is truthy. This holds for the
  methods of a `string`, an array, or a scalar class, and for a record's or a
  sum's declared methods (`fun T.m`) alike, so
  `if v.m { v.m() } else { ... }` dispatches on whether the receiver's type
  implements `m`;
- a name the type does not have is `null` (`never?`), which is always falsy.

Because a bare `null` is statically false and any other value statically true,
an `if` over a member access is decided while checking. The arm that cannot run
is neither type-checked nor emitted, so a single generic body may hold arms that
only type for _some_ of its instantiations:

```brass
type Segments = { parts: string[] }

const SEP = "/"

fun describe(s) -> string {
    if s.parts {
        return "record: {s.parts.join(SEP)}"   // only for Segments
    } else if s.split {
        return "string: {s.split(SEP).len()}"  // only for string
    } else {
        return "array: {s.len()}"              // only for an array
    }
}

println(describe(Segments { parts: ["usr", "lib"] }))
println(describe("a/b/c"))
println(describe(["x", "y"]))
```

`s.split(...)` would not type against `Segments`, and `s.parts` names no member
of `string`, but each arm is reached only by the receiver it fits. This is how
a library takes "a string, an array of strings, or a `Path`" through one
parameter without overloading or union types.

Every receiver class supports the test. A scalar (`int32`, `bool`, ...)
carries only its stdlib methods, so an unknown name on one reads as `null`
like everywhere else, which is what lets a presence-dispatching body
instantiate at scalars too.

The prelude turns this into a direct **type test** for the primitives: each
primitive type implements only its own `is_<type>` method (`is_string`,
`is_int32`, `is_uint8`, ..., `is_bool`, `is_float64`, `is_array`), so
`v.is_string` is present (truthy) exactly when `v` is a `string`, and
reads as `null` on every other type:

```brass
fun describe(v) -> string {
    if v.is_string {
        return "string"
    } else if v.is_int32 {
        return "int32"
    }
    return "other"
}

println(describe("a"))
println(describe(3))
println(describe(1.5))
```

Calling the method (`v.is_string()`) returns `true`: it only exists on the
matching type, so the call is only reachable there. Records and sums carry
none of these members.

## Building a value field by field

An annotated `let` may omit its initializer. The binding must then be
definitely assigned before it is read, either all at once, or, for a record,
one field at a time. A `fields` loop that stores into every field of such a
binding initializes it completely:

```brass
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

Together these make deserialization (filling a struct from a name-keyed
source) expressible without any per-type boilerplate beyond the field walk.
The target's own field names drive the lookup, and a missing key is a decode
error naming the field:

```brass
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

This turns a whole recursive JSON-to-struct decoder into one method. This is
exactly how the `data.json` library implements `JsonValue.into` (abridged):

```brass norun
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

## Compile-time cost

Reflective decoding is specialized at compile time: each `(receiver, method,
target type)` triple becomes a generated concrete method, and injecting those
changes the program, so the whole front end type-checks a second time. A
keyed build costs roughly twice a plain one; the caches described in
[Performance & caching](/references/performance/) absorb that cost: the
`.czcache` makes every unchanged build skip both passes entirely.
