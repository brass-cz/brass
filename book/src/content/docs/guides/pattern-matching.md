---
title: "Pattern matching"
description: "match expressions, exhaustiveness, patterns, and if let."
---

## `match`

`match` is an expression that takes a value apart. Over a sum type it is
checked for **exhaustiveness** — forgetting a variant is a compile error:

```prepoly
type Shape =
    | Circle { radius: float64 }
    | Rectangle { width: float64, height: float64 }
    | Point

fun describe(s: Shape) -> string {
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

```
circle r=2.0
rect 3.0x4.0
a point
```

A variant pattern binds the variant's fields by name. Bind only some of them
and omit the rest with `..`:

```prepoly
type Holder =
    | Full { data: int32, tag: int32 }
    | Empty

fun first(h: Holder) -> int32 {
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

```prepoly
fun classify(n: int32) -> string {
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

Matching on strings works the same way — see the expression-tree example in
[Types and methods](/guides/types/#sum-types), which matches on `"+"` and `"*"`.

## `if let`

When you only care about a single variant, `if let` matches it and binds its
fields, without requiring the other arms:

```prepoly
type Shape =
    | Circle { radius: float64 }
    | Rectangle { width: float64, height: float64 }
    | Point

fun radius_of(s: Shape) -> float64? {
    if let Circle { radius } = s {
        return radius
    }
    return null
}
```

`if let` is also the idiomatic way to consume nullable results such as
`s.find(sub)` or `T.from(v)` (structural conversion) — the bound name is the
non-null value:

```prepoly
if let idx = "hello".find("ll") {
    println("found at {idx}")   // found at 2
}
```

The full pattern grammar (array patterns, negative literals, nesting) is in
the [syntax reference](/references/syntax/#patterns).
