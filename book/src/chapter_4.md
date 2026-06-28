# Chapter 4: `null` and `Result`

prepoly has a `null` type and a `Result` type.

Let's see an example:

```prepoly
fun double(a: int32?) {
    if a {
        return a * 2
    } else {
        return error("null")
    }
}

println(double(2))
println(double(null))
```

The variable `a` of the function `double` has the type `int32?`.
The `?` means that the value may be `null`.
A value that may be `null` must be checked with an `if` expression.

Calling the `error` function makes the return value a `Result.Err`.
When a function returns a plain value where a `Result` is expected, it is wrapped as `Result.Ok`.

So the output of the above program is as follows:

```
Result.Ok {
    value: 4,
}
Result.Err {
    error: null,
}
```

We can omit the type annotation for nullable types.
But if a function receives `null` without a null check, the type check fails and the function is not executed.
