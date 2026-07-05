---
title: "Input and output"
description: "Printing, reading input, and file I/O."
---

## Printing

`print(value)` writes a value's text to standard output; `println(value)` adds
a newline. Both take a single argument — combine values with string
interpolation:

```prepoly
let a = 6
let b = 7
println("{a} * {b} = {a * b}")   // 6 * 7 = 42
```

Any value prints, including records and arrays:

```prepoly
type Point = { x: int32, y: int32 }
println(Point { x: 1, y: 2 })
```

## Reading input

`input()` reads one line from standard input, without the trailing newline.
It returns `string!` (reading can fail), so unwrap it with `!` — at the top
level a failure just ends the program with the error — or handle it with
`match`:

```prepoly
println("What's your name?")
let name = input()!
println("Hello, {name}!")
```

## Files

`read_file(path)` and `write_file(path, content)` cover whole-file text I/O.
Both return a Result. In a quick script, unwrap with `!` and let a failure
stop the program:

```prepoly
let path = "demo.txt"
write_file(path, "line one\nline two")!
let content = read_file(path)!
for line in content.split("\n") {
    println("  {line}")
}
```

Where a failure should be handled instead, match on the Result:

```prepoly
match read_file("missing.txt") {
    Ok { value } => println(value),
    Err { error } => println("read failed: {error}"),
}
```

For finer control, `open(path, mode)` returns a `File!`; a `File` has
`read(n)`, `write(bytes)`, `seek`, `size()`, and `close()`, all returning
Results, plus the `File.stdin()` / `File.stdout()` constructors. See the
[standard library reference](/references/stdlib/#files) for the signatures.

Note: file I/O runs on the native runtime. The REPL interpreter (and the
browser playground) refuses it at runtime — see the
[execution model reference](/references/execution/).
