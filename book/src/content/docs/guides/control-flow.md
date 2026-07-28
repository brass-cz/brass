---
title: "Control flow"
description: "if as an expression, while, for over arrays and ranges, break and continue."
---

Brass has the usual control-flow constructs: `if`/`else`, `while`, `for`,
`break`, and `continue`. A distinctive point is that `if` (and `match`, covered
in [Pattern matching](/guides/pattern-matching/)) are _expressions_: they yield a
value.

## `if` is an expression

```brass
fun grade(score) {
    let result = if score >= 60 { "pass" } else { "fail" }
    return result
}

println(grade(72))   // pass
println(grade(31))   // fail
```

`else if` chains work as you would expect:

```brass
fun size_of(n) {
    if n < 10 {
        return "small"
    } else if n < 100 {
        return "medium"
    } else {
        return "large"
    }
}
```

## Type tests: `if value: Type`

An `if` condition can test a value's **type**: `if value: Type { ... }`. The
test is answered at compile time, separately for each concrete type a generic
function is called with -- there is nothing to check at run time. The first
arm whose type matches is the one that is compiled; the arms that do not match
are not even type-checked for that call, so each arm may use the value in ways
that only make sense for its own type:

```brass
fun length(val) {
    const bytes = if val: infer {
        to_bytes(val)      // `infer` takes the type this arm needs: string
    } else if val: uint8[] {
        val                // already bytes
    } else if val: infer[] {
        val                // any other array; val keeps its own element type
    } else {
        return error("length: unsupported value")
    }
    return bytes.len()
}

// Instances whose live path never reaches `error(...)` return a plain value...
println(length("hello") + length([1, 2, 3]))   // 8

// ...and only the instance that actually selects the `else` arm is fallible.
match length(true) {
    Ok { value } => println("unreachable"),
    Err { error } => println("bool: unsupported"),
}
```

A bare `infer` in the tested type is a hole filled by what the arm itself
requires: `to_bytes` accepts a `string`, so the first arm selects exactly the
string case. A hole nothing constrains matches any type -- `infer[]` reads as
"any array".

Unselected arms contribute nothing to an instance: the `error(...)` above
makes only the `length(true)` instance return a `Result`, and each instance's
return type comes from its own live path alone -- one arm may return an
`int32` and another a `string`, each serving its own callers.

The test also accepts [structural subtyping](/guides/types/#structural-subtyping):
a record matches any tested type whose fields and methods it satisfies, so a
type test can dispatch on capability rather than on an exact name:

```brass
type Point = { x: int32, y: int32 }

fun describe(v) -> string {
    if v: anonymous { x: int32 } {
        return "x = {v.x}"
    } else if v: string {
        return v
    }
    return "something else"
}

println(describe(Point { x: 7, y: 9 }))   // x = 7
println(describe("plain text"))           // plain text
println(describe(3.5))                    // something else
```

Matching never converts the value: an `int32` does not select an `int64` arm,
a `T` does not select a `T?` arm, and inside the selected arm the value keeps
its own concrete type. The exact matching rules are in the
[type-system reference](/references/types/#type-tests).

## `while`

Here is the Collatz step counter, where `while` runs as long as the condition holds:

```brass
fun collatz_steps(n) {
    let count = 0
    let x = n
    while x != 1 {
        if x % 2 == 0 {
            x = x / 2
        } else {
            x = 3 * x + 1
        }
        count += 1
    }
    return count
}

for n in [6, 7, 27] {
    println("collatz({n}) = {collatz_steps(n)} steps")
}
```

## `for` over arrays and ranges

`for x in xs` iterates the elements of an array. The bracket form `[lo..hi]`
builds the half-open integer range `lo, lo+1, ..., hi-1`, so counting loops
look like this:

```brass
let sum = 0
for i in [1..11] {
    sum += i
}
println(sum)   // 55
```

## `break` and `continue`

`continue` skips to the next iteration, `break` exits the loop:

```brass
let sum = 0
for n in [1, 2, 3, 4, 5, 6, 7, 8] {
    if n % 2 == 1 {
        continue
    }
    if n > 6 {
        break
    }
    sum += n
}
println("sum of evens up to 6 = {sum}")   // 12
```

There is no statement terminator: a newline ends a statement. A line continues
onto the next when it ends with a binary operator or when the next line starts
with `.` (a method chain). See [Syntax](/references/syntax/) for the exact
rules.
