---
title: "Hello, world!"
description: "Your first Brass program: printing, running, and checking."
---

This chapter walks through a first Brass program.

Write the following into a `hello.cz` file.

```brass
println("Hello, world!")
```

Then, execute the program:

```bash
brass hello.cz
```

This prints:

```
Hello, world!
```

A Brass source file is a script: top-level statements run from top to bottom.
You can also define a `main` function, which is called after the top-level
statements have run:

```brass
fun main() {
    println("Hello, world!")
}
```

This produces the same output.

## Checking without running

An ordinary run checks each function before that function can execute, but it
does not wait for unused functions. To check the whole program without
executing it, use `brass check`:

```bash
brass check hello.cz
```

It prints nothing when the program is well-typed, and exits 0; otherwise it
prints the type errors and exits non-zero.
Running `brass` with no arguments starts an interactive REPL.

### A run only checks what it runs

`brass hello.cz` checks **lazily**: the run's verdict covers the code the run
actually needs. A type error in a function the run never calls does not stop
the run:

```brass norun
fun broken() -> int32 {
    return "oops"    // a type error -- but nothing calls broken()
}

println("Hello, world!")
```

`brass hello.cz` prints `Hello, world!` and exits 0. `brass check hello.cz`
reports the error in `broken`.

What this means in practice:

- **A green run is not a full type check.** Use `brass check` for the
  whole-program verdict, e.g. in CI, before a commit, or after a refactor.
- Errors in code the run does need still stop it. An error in the top-level
  statements or in `main` aborts before anything executes; an error in a
  function first reached mid-run stops the run right there, though output
  already produced stands and the run exits non-zero. The unit is the whole
  function: an error anywhere in a function the run calls counts, even in a
  branch execution would never take.
- Unused code may continue checking in the background until the program
  exits, but its diagnostics never change the current run's outcome.
- `brass --eager hello.cz` runs with the check-everything-first behavior
  (identical to `brass check` followed by the run). The REPL and the
  interpreter back end always check eagerly.

See [Execution model](/references/execution/) for the full rules.

## Running as a script

`#` starts a line comment, so a source file may begin with a **shebang** line.
That lets you run a Brass file directly, like a shell script:

```brass
#!/usr/bin/env brass
println("Hello from a script!")
```

Mark the file executable once, then run it by name:

```bash
chmod +x hello.cz
./hello.cz
```

The shebang line is ordinary comment syntax, so the same file still works with
`brass hello.cz`, `brass check hello.cz`, and on systems that do not use
shebangs at all.

## GCD: Greatest Common Divisor

A slightly more practical example: a `gcd` function computing the greatest
common divisor.

```brass
fun gcd(a, b) {
    if b == 0 {
        return a
    } else {
        return gcd(b, a % b)
    }
}

println(gcd(48, 36))
```

This outputs `12`.

No type annotation was written: parameter and return types are inferred. The
program is still statically typed, so passing a string to `gcd` would be
rejected before execution.

## Variables and arrays

`const` declares an immutable variable, `let` a mutable one.

```brass
const pi = 3.14159   // reassigning is a compile error
let count = 0
count += 1
```

The following program calculates the gcd of all elements in an array:

```brass
fun gcd(a, b) {
    if b == 0 {
        return a
    } else {
        return gcd(b, a % b)
    }
}

const elems = [16, 36, 72, 192]
let result = elems[0]
for elem in elems.slice(1, elems.len()) {
    result = gcd(result, elem)
}
println("GCD is {result}")
```

This program outputs `GCD is 4`.

The `{result}` inside the string is **string interpolation**: `{expr}`
evaluates the expression and inserts its text into the string.

The following chapters introduce each language feature the same way, by
example. For exhaustive rules, see the [references](/references/syntax/).
