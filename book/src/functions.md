# Functions and closures

## Type inference

Functions are declared with `fun`. Parameter and return annotations are
optional — when omitted, they are inferred:

```prepoly
fun add(a, b) {
    return a + b
}

fun scale(x: float64, factor: float64) -> float64 {
    return x * factor
}

println(add(2, 3))          // 5
println(scale(1.5, 2.0))    // 3.0
```

An unannotated function is polymorphic: `add` also works for floats or
strings, because the body only requires a type that supports `+`. Each call
site is checked with the actual argument types, so `add(1, "x")` is still a
compile error.

## Closures

A closure is written `(params) -> body`. The body is a single expression, or a
block that returns with `return`:

```prepoly
let inc = (n: int32) -> n + 1
let shout = (s: string) -> {
    return s.to_upper() + "!"
}

println(inc(41))        // 42
println(shout("hey"))   // HEY!
```

Closures capture their environment **by reference**, so captured variables stay
shared and mutable across calls:

```prepoly
fun make_accumulator(initial: int32) {
    let total = initial
    return (amount: int32) -> {
        total += amount
        return total
    }
}

let acc = make_accumulator(100)
println(acc(10))   // 110
println(acc(20))   // 130
```

## Higher-order functions

Functions and closures are values, so they can be passed around:

```prepoly
fun apply_twice(f, x) {
    return f(f(x))
}

let inc = (n: int32) -> n + 1
println(apply_twice(inc, 10))   // 12
```

The array helpers of the standard library are the everyday use of this — a
chain may be broken across lines when the next line starts with `.`:

```prepoly
let result = [3, 1, 4, 1, 5, 9]
    .filter((x) -> x > 2)
    .map((x) -> x * 10)
    .fold(0, (a, b) -> a + b)
println("chain result = {result}")   // 210
```

## Parameters and mutation

When a parameter has no annotation, prepoly infers not just its type but also
how it is passed. A parameter the body only *reads* is a cheap shared
reference. A parameter the body *mutates* becomes a private deep copy, so the
mutation stays inside the function:

```prepoly
fun double(a) {
    for e in a {
        e *= 2
    }
}

let arr = [1, 2, 3]
double(arr)
println(arr)   // [1, 2, 3] — double worked on its own copy
```

To mutate the caller's value through a function, annotate the parameter
`ref(mut(T))` — a mutable reference writes through:

```prepoly
fun double_through(a: ref(mut(int32[]))) {
    for e in a {
        e *= 2
    }
}

let arr = [1, 2, 3]
double_through(arr)
println(arr)   // [2, 4, 6]
```

This default means a function can never mutate your data unless its signature
says so. The complete rules (including `ref(T)`, `mut(T)`, and `infer`) are in
the [type system reference](references/types.md#parameter-passing).
