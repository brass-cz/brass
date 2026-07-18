---
title: "Input and output"
description: "Printing, reading input, and file I/O."
---

## Printing

`print(value)` writes a value's text to standard output; `println(value)` adds
a newline. Both take a single argument, so combine values with string
interpolation:

```brass
let a = 6
let b = 7
println("{a} * {b} = {a * b}")   // 6 * 7 = 42
```

Any value prints, including records and arrays:

```brass
type Point = { x: int32, y: int32 }
println(Point { x: 1, y: 2 })
```

## Reading input

`input()` reads one line from standard input, without the trailing newline.
It returns `string!` (reading can fail). Unwrap it with `!`, which at the top
level ends the program with the error on failure, or handle it with
`match`:

```brass
println("What's your name?")
let name = input()!
println("Hello, {name}!")
```

## Files

Whole-file text I/O lives in `std.fs`, not in the implicit prelude.
Import it first; from a repo checkout, build the plugins with `std/build.sh`
and declare the `std` package as described in the
[standard library reference](/references/stdlib/#stdfs).
`read_file(path)` and `write_file(path, content)` both return a Result. In a
quick script, unwrap with `!` and let a failure stop the program:

```brass norun
import std.fs.{ read_file, write_file }

let path = "demo.txt"
write_file(path, "line one\nline two")!
let content = read_file(path)!
for line in content.split("\n") {
    println("  {line}")
}
```

Where a failure should be handled instead, match on the Result:

```brass norun
import std.fs.read_file

match read_file("missing.txt") {
    Ok { value } => println(value),
    Err { error } => println("read failed: {error}"),
}
```

For finer control, `File.open(path, mode)` returns a `File!`; a `File` has
`read(n)`, `write(bytes)`, `seek`, `size()`, and `close()`, all returning
Results, plus the `File.stdin()` / `File.stdout()` / `File.stderr()`
constructors. See the
[standard library reference](/references/stdlib/#stdfs) for the
signatures.

Note: the native `brass` and `brass repl` can both use the plugin-backed
`std` modules, but the browser playground cannot load plugins, so file I/O
examples are not runnable there.
