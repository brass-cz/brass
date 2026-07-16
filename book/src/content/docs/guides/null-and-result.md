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
fun first_even(nums) -> int32? {
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
fun parse_positive(s) {
    let n = int32.parse(s)!          // `!` returns early on a parse error
    if n < 0 {
        return error("negative number: {n}")
    }
    return n                          // implicitly wrapped in Result.Ok
}

for s in ["42", "-5", "abc"] {
    match parse_positive(s) {
        Ok { value } => println("parsed {s} -> {value}"),
        Err { error } => println("failed {s} -> {error.value}"),
    }
}
```

Three things are happening here:

- The postfix **`!` operator** propagates errors: `expr!` unwraps an `Ok`
  value, or returns the `Err` from the enclosing function immediately.
- A `Result` is consumed by **matching** on its variants, `Ok { value }` and
  `Err { error }`.
- The `Err` payload is an **`Error` record**: `error(x)` wraps `x` together
  with the call site's position, and a builtin failure forwarded by `!` (the
  parse error here) is wrapped the same way at the propagation site. The
  original value is `error.value`; the position and any
  [context frames](#error-traces-and-context) ride along.

## `!` at the top level and in `main`

You do not need to wrap everything in a fallible function to use `!`. At the
module top level (and inside `main`), a failed `!` simply **stops the
program**: the error is printed and the process exits non-zero. On success it
unwraps in place, which makes short scripts read naturally:

```prepoly
let n = int32.parse("123")!   // unwraps to 123 right here
println(n + 1)
```

If the parse had failed, the program would have ended with

```text
unhandled error: cannot parse `12x` as integer
```

instead of continuing with a bad value. So the beginner-friendly default is:
write `!` after any fallible call and let a failure stop the script; reach
for `match` only where you want to _handle_ the error.

## Error traces and `context`

An error raised by `error(..)` remembers **where** it was raised, and
`context("...")` lets every layer on the way out say what it was doing.
When the failure finally goes unhandled, the whole story prints as a nested
trace, newest step first:

```prepoly
fun read_config() -> infer! {
    return error("missing key `port`")
}

fun start_server() -> infer! {
    return read_config().context("starting the server")
}

start_server()!
```

```text
[main.pp:6:12] unhandled error: starting the server
    [main.pp:2:12] unhandled error: missing key `port`
```

No plumbing is needed: `error` and `context` pick up their call site through
an implicit `Location` argument the compiler fills in. When you handle the
error yourself, the same information is on the `Error` record — `error.value`
is the raised value, `error.location` the position, and `error.display()`
renders the trace text above. A failure that never went through
`error(..)`/`context` (a plain builtin error hit at the top level) keeps the
short `unhandled error: <message>` form.

## Your own Result type

A library that wants to carry more than `Ok`/`Err` can declare its own sum
**as a subtype of `Result`**: it must have exactly the `Ok` and `Err`
variants, and each variant may add fields. The `!` operator (and any other
place a `Result` is expected) accepts it by rebuilding the value as a plain
`Result`, dropping the extra fields:

```prepoly
type Lookup: Result =
    | Ok {
        value: int32
        source: string
    }
    | Err {
        error: string
    }

fun find_port(name: string) -> Lookup {
    if name == "http" {
        return Lookup.Ok { value: 80, source: "well-known" }
    }
    return Lookup.Err { error: "unknown service `{name}`" }
}

fun connect(name: string) -> infer! {
    let port = find_port(name)!      // Lookup propagates like a Result
    return "{name}:{port}"
}

fun main() {
    println(connect("http")!)
    match find_port("gopher") {      // or match Lookup directly, source and all
        Ok { value, source } => { println("{value} via {source}") }
        Err { error } => { println("no port: {error}") }
    }
}
```

Matching the `Lookup` itself keeps the extra `source` field; going through
`!` trades it for plain-`Result` interoperability. Two structurally
identical sums that do **not** declare the relationship stay unrelated — see
[the reference](/references/syntax-sugar/#declared-sum-subtyping) for the
exact rules, including how a module can instead shadow `Result` outright.

## Fallible conversions

Conversions that can fail return a Result. `intN.from(x)` range-checks,
and `T.parse(s)` parses a string:

```prepoly
let small = uint8.from(42)!         // ok
let too_big = uint8.from(300)       // Result.Err: out of range
println(too_big)

let n = int32.parse("123")!         // 123
let f = float64.from(n) + 0.5       // no `!`: float64.from always succeeds
let s = string.from(true)           // "true" — string.from always succeeds
println("{n} {f} {s}")
```

Note the difference: `intN.from` and `T.parse` return `T!` because they can
fail, while `float64.from` and `string.from` are total and return the plain
value. The
[type system reference](/references/types/#numeric-conversions) lists the
whole conversion family, including the implicit value-preserving conversions
between numeric types.

## Propagating null with `!`

`!` also works on a **nullable** operand. The value case unwraps; a `null`
returns **null itself** from the enclosing function, so that function's
return type gains an outer `?`:

```prepoly
fun first_even(nums) -> int32? {
    for n in nums {
        if n % 2 == 0 {
            return n
        }
    }
    return null
}

// first_even's null flows straight out of `!`, so double_first_even
// is inferred as (int32[]) -> int32? -- no Result involved.
fun double_first_even(nums) {
    let n = first_even(nums)!   // int32? -> int32, or return null now
    return n * 2
}

let d = double_first_even([1, 3, 4])
if d {
    println("doubled {d}")
} else {
    println("no even number")
}
```

A body can mix all three return kinds -- plain values, `error(...)`, and a
nullable `!`. The plain and error returns make it a `Result`, and the null
propagation wraps that in `?`:

```prepoly
fun f(c: int32) {
    if c == 0 {
        return 1          // Result.Ok { value: 1 }
    } else if c == 1 {
        error("a")!       // Result.Err — the payload is an Error wrapping "a"
    } else {
        null!             // null itself
    }
}

// f is (int32) -> Result<int32, Error>?: narrow the `?` first, then match.
let r = f(0)
if r {
    match r {
        Ok { value } => println("ok {value}"),
        Err { error } => println("err {error.value}"),
    }
} else {
    println("null")
}
```

At the top level and in `main`, a `null` hit by `!` stops the program the
same way an `Err` does: it aborts with
`` unhandled error: null value propagated by `!` `` and a non-zero exit --
the null has nowhere to go, and silently succeeding would hide the failure.

## Absent fields become `null` in conditions

Inside a conditional, an inference failure — such as accessing a field the
value does not have — becomes `null` instead of a compile error. This lets a
structurally typed function probe for optional fields:

```prepoly
fun get_name(person) {
    if person.name {
        return person.name
    } else {
        return "no name"
    }
}

println(get_name({ name: "Asimov" })) // Asimov
println(get_name({ age: 20 }))        // no name
```
