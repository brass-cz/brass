---
title: "Pattern matching"
description: "match expressions, exhaustiveness, patterns, and if let."
---

## `match`

`match` is an expression that takes a value apart. Over a sum type it is
checked for **exhaustiveness**: forgetting a variant is a compile error:

```brass
type Shape =
    | Circle { radius: float64 }
    | Rectangle { width: float64, height: float64 }
    | Point

fun describe(s) {
    return match s {
        Circle { radius } => "circle r={radius}",
        Rectangle { width, height } => "rect {width}x{height}",
        Point => "a point",
    }
}

for s in [
    Shape.Circle { radius: 2.0 },
    Shape.Rectangle { width: 3.0, height: 4.0 },
    Shape.Point,
] {
    println(describe(s))
}
```

A variant pattern binds the variant's fields by name. Bind only some of them
and omit the rest with `..`:

```brass
type Holder =
    | Full { data: int32, tag: int32 }
    | Empty

fun first(h) {
    return match h {
        Holder.Full { data, .. } => data,
        Holder.Empty => 0,
    }
}
```

The variant name may be written bare (`Full { .. }`) or qualified
(`Holder.Full { .. }`).

## Literal patterns and the wildcard

Patterns also include literals (integers, floats, strings, `true`/`false`,
`null`) and the wildcard `_`, which matches anything:

```brass
fun classify(n) {
    return match n {
        0 => "zero",
        1 => "one",
        _ => "many",
    }
}

for n in [0, 1, 2, 9] {
    println("{n} is {classify(n)}")
}
```

Matching on strings works the same way; see the expression-tree example in
[Types and methods](/guides/types/#sum-types), which matches on `"+"` and `"*"`.

An integer literal pattern (a negative one like `-1` included) is typed like
a literal flowing into a variable of the scrutinee's type: it must fit that
type. On a nullable scrutinee a value literal matches a present value equal to
it, and `null` matches the absent one (a variant or record pattern likewise
matches only a present value, and a `match` over a nullable sum needs a
`null` or `_` arm):

```brass
fun classify(n: int64?) -> string {
    return match n {
        -1 => "minus one",
        null => "none",
        _ => "other",
    }
}
```

## `if let`

When you only care about a single variant, `if let` matches it and binds its
fields, without requiring the other arms:

```brass
type Shape =
    | Circle { radius: float64 }
    | Rectangle { width: float64, height: float64 }
    | Point

fun radius_of(s) {
    if let Circle { radius } = s {
        return radius
    }
    return null
}
```

`if let` is also the idiomatic way to consume nullable results such as
`s.find(sub)` or `T.from(v)` (structural conversion); the bound name is the
non-null value:

```brass
if let idx = "hello".find("ll") {
    println("found at {idx}")   // found at 2
}
```

The full pattern grammar (array patterns, negative literals, nesting) is in
the [syntax reference](/references/syntax/#patterns).
