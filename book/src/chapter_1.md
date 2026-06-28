# Chapter 1: Hello, world!

Let's write your first prepoly program!

Write the following program into a `hello.pp` file.

```prepoly
println("Hello, world!")
```

Then, execute the program:

```bash
prepoly hello.pp
```

Output is as follows:

```
Hello, world!
```

You can define a main function as follows:

```prepoly
fun main() {
    println("Hello, world!")
}
```

The execution result is the same as the previous one.



## GCD: Greatest Common Divisor

Next, let's write a practical example.

We can write a `gcd` function, which calculates the greatest common divisor, as follows:

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


## Using an array

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
