---
title: "Nullable and Result"
description: "Nullable types, the Result type, error propagation, and fallible conversions."
---

prepoly has no exceptions. "May be absent" is expressed with the nullable type
`T?`, and "may fail" with the Result type `T!`.

## Nullable types

`T?` means the value may be `null`. A nullable value must be _narrowed_ with an
`if` guard before it can be used:

```prepoly
// Returns the first even number, or null if there is none.
fun first_even(nums: int32[]) -> int32? {
    for n in nums {
        if n % 2 == 0 {
            return n
        }
    }
    return null
}

let found = first_even([1, 3, 4, 7])
if found {
    // Inside the guard, `found` is narrowed from int32? to int32.
    println("first even = {found}")
}

let none = first_even([1, 3, 5])
if !none {
    println("no even number found")
}
```

Using a nullable value without a check — say `found + 1` before the `if` — is
a compile error. An early-return guard also narrows: after
`if !x { return ... }`, the value `x` is a plain `T` for the rest of the
function.

## Result and `error`

`T!` is a `Result` holding either a success value (`Ok`) or an error (`Err`).
Call `error(x)` to produce an error; returning a plain value where a `Result`
is expected wraps it as `Ok` automatically:

```prepoly
fun parse_positive(s: string) {
    let n = int32.parse(s)!          // `!` returns early on a parse error
    if n < 0 {
        return error("negative number: {n}")
    }
    return n                          // implicitly wrapped in Result.Ok
}

for s in ["42", "-5", "abc"] {
    match parse_positive(s) {
        Ok { value } => println("parsed {s} -> {value}"),
        Err { error } => println("failed {s} -> {error}"),
    }
}
```

```
parsed 42 -> 42
failed -5 -> negative number: -5
failed abc -> cannot parse `abc` as integer
```

Two things are happening here:

- The postfix **`!` operator** propagates errors: `expr!` unwraps an `Ok`
  value, or returns the `Err` from the enclosing function immediately.
- A `Result` is consumed by **matching** on its variants, `Ok { value }` and
  `Err { error }`.

## Fallible conversions

Conversions that can fail return a Result. `intN.from(x)` range-checks,
and `T.parse(s)` parses a string:

```prepoly
fun main() {
    let small: uint8 = uint8.from(42)!  // ok
    let too_big = uint8.from(300)       // Result.Err: out of range
    println(too_big)

    let n = int32.parse("123")!         // 123
    let f = float64.from(n) + 0.5       // no `!`: float64.from always succeeds
    let s = string.from(true)           // "true" — string.from always succeeds
    println("{n} {f} {s}")
}
```

(The `!` operator needs an enclosing function, so this example defines `main`.)

Note the difference: `intN.from` and `T.parse` return `T!` because they can
fail, while `float64.from` and `string.from` are total and return the plain
value. The
[type system reference](/references/types/#numeric-conversions) lists the
whole conversion family, including the implicit value-preserving conversions
between numeric types.

## Absent fields become `null` in conditions

Inside a conditional, an inference failure — such as accessing a field the
value does not have — becomes `null` instead of a compile error. This lets a
structurally typed function probe for optional fields:

```prepoly
fun get_name(person) -> string {
    if person.name {
        return person.name
    } else {
        return "no name"
    }
}

println(get_name({ name: "Asimov" })) // Asimov
println(get_name({ age: 20 }))        // no name
```
