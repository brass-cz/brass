---
title: "Collections and strings"
description: "Arrays, strings, and HashMap from the core library."
---

The core library is an implicit prelude: its helpers are available in
every program with no import. This chapter tours the everyday ones; the
complete list with signatures is in the
[standard library reference](/references/stdlib/).

## Arrays

An array literal is `[1, 2, 3]`. Arrays index with `arr[i]`, grow with
`push`, and know their `len`:

```brass
let nums = [5, 3, 8, 1, 9, 2]
println("len      = {nums.len()}")
println("sorted   = {nums.sort()}")
println("reversed = {nums.reverse()}")
println("doubled  = {nums.map((x) -> x * 2)}")
println("evens    = {nums.filter((x) -> x % 2 == 0)}")
println("sum      = {nums.fold(0, (a, b) -> a + b)}")
println("contains 8 = {nums.contains(8)}")
println("slice 1..4 = {nums.slice(1, 4)}")
```

Arrays also support in-place editing:

```brass
let a = [1, 2, 3]
a.insert(1, 10)      // [1, 10, 2, 3]
let r = a.remove(0)  // r = 1, a = [10, 2, 3]
let last = a.pop()   // nullable: 3 here, null when the array is empty
```

The helpers compose nicely into chains:

```brass
let sum_of_squares = [1, 2, 3, 4, 5, 6]
    .filter((x) -> x % 2 == 0)
    .map((x) -> x * x)
    .fold(0, (a, b) -> a + b)
println(sum_of_squares)   // 56
```

## Strings

Strings are UTF-8 and immutable; `+` concatenates. The prelude provides the
usual utilities as methods:

```brass
let csv = "alice,bob,carol"
let names = csv.split(",")
println("count  = {names.len()}")
println("joined = {names.join(" | ")}")
println("upper  = {"hello".to_upper()}")
println("trimmed = '{"   spaced   ".trim()}'")
println("starts  = {"brass".starts_with("pre")}")
println("replace = {"a-b-c".replace("-", "+")}")
```

`s.find(sub)` returns the byte offset of a substring as `int64?` (`null` when
absent), and `s.chars()` splits into one-character strings; there is no
separate character type:

```brass
for c in "héllo".chars() {
    print(c)
    print(".")
}
println("")   // h.é.l.l.o.
```

String positions are UTF-8 **byte** offsets: `len` and `find` agree
on byte positions, and a multibyte character counts as several bytes.

## HashMap

`HashMap` lives in the core module `core.collections` and, like the rest
of `core`, is in scope with no import. `HashMap.new()` takes no arguments;
the key and value types are inferred from the first insertion:

```brass
let ages = HashMap.new()
ages.set("alice", 30)
ages.set("bob", 25)

println(ages.get_or("alice", 0))     // 30
println(ages.contains_key("carol"))  // false
println(ages.size())                 // 2

let maybe = ages.get("bob")          // int32? — null when absent
if maybe {
    println("bob is {maybe}")
}

for pair in ages.pairs() {
    println("{pair[0]} -> {pair[1]}")
}
```

`keys()`, `values()`, `delete(k)`, `clear()`, and
`HashMap.from_pairs([[k, v], ...])` round out the API. Keys may be any type
that compares with `==`: integers, strings, even records.
