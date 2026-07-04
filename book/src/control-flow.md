# Control flow

prepoly has the usual control-flow constructs: `if`/`else`, `while`, `for`,
`break`, and `continue`. A distinctive point is that `if` (and `match`, covered
in [Pattern matching](pattern-matching.md)) are *expressions* — they yield a
value.

## `if` is an expression

```prepoly
fun grade(score: int32) -> string {
    let result = if score >= 60 { "pass" } else { "fail" }
    return result
}

println(grade(72))   // pass
println(grade(31))   // fail
```

`else if` chains work as you would expect:

```prepoly
fun size_of(n: int32) -> string {
    if n < 10 {
        return "small"
    } else if n < 100 {
        return "medium"
    } else {
        return "large"
    }
}
```

## `while`

Here is the Collatz step counter — `while` runs as long as the condition holds:

```prepoly
fun collatz_steps(n: int32) -> int32 {
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

```
collatz(6) = 8 steps
collatz(7) = 16 steps
collatz(27) = 111 steps
```

## `for` over arrays and ranges

`for x in xs` iterates the elements of an array. The bracket form `[lo..hi]`
builds the half-open integer range `lo, lo+1, ..., hi-1`, so counting loops
look like this:

```prepoly
let sum = 0
for i in [1..11] {
    sum += i
}
println(sum)   // 55
```

## `break` and `continue`

`continue` skips to the next iteration, `break` exits the loop:

```prepoly
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
with `.` (a method chain) — see [Syntax](references/syntax.md) for the exact
rules.
