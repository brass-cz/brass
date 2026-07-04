# Hello, world!

Let's write your first prepoly program!

Write the following program into a `hello.pp` file.

```prepoly
println("Hello, world!")
```

Then, execute the program:

```bash
prepoly hello.pp
```

The output is as follows:

```
Hello, world!
```

A prepoly source file is a script: top-level statements run from top to bottom.
You can also define a `main` function, which is called after the top-level
statements have run:

```prepoly
fun main() {
    println("Hello, world!")
}
```

The execution result is the same as the previous one.

## Checking without running

Every function is fully type-checked before it runs. To type-check a program
without executing it, use `prepoly check`:

```bash
prepoly check hello.pp
```

It prints `ok` when the program is well-typed, or the type errors otherwise.
Running `prepoly` with no arguments starts an interactive REPL.

## GCD: Greatest Common Divisor

Next, let's write a practical example.

We can write a `gcd` function, which calculates the greatest common divisor,
as follows:

```prepoly
fun gcd(a, b) {
    if b == 0 {
        return a
    } else {
        return gcd(b, a % b)
    }
}

println(gcd(48, 36))
```

This outputs `12`, which is correct!

Note that we didn't write a single type annotation: parameter and return types
are inferred. The program is still statically typed — passing a string to
`gcd` would be rejected before execution.

## Variables and arrays

We can use `const` to declare an immutable variable and `let` to declare a
mutable variable.

```prepoly
const pi = 3.14159   // reassigning is a compile error
let count = 0
count += 1
```

The following program calculates the gcd of all elements in an array:

```prepoly
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

Now you have seen a complete little program. The following chapters introduce
each language feature the same way — by example. For exhaustive rules, see the
[references](references/syntax.md).
