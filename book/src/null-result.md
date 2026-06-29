# `null` and `Result`

prepoly has `null` type and `Result` type.

Let's see an example:

```prepoly
fun double(a: int32?) -> int32! {
    if a {
        return a * 2
    } else {
        return error("null")
    }
}

println(double(2))
println(double(null))
```

The variable `a` of the function `double` has a type `int32?`.
The character `?` means that the value may become `null` type.
Some value that may become `null` must be checked by `if` expression.

If you use `error` function, the variant of return value is `Result.Err`.
The type of the value that type is other than `Result` but must be `Result` type become `Result.Ok`.
The `Result` type that returns `int32` as its value is denoted as `int32!`.

So the output of the above program is as follows:

```
Result.Ok {
    value: 4,
}
Result.Err {
    error: null,
}
```

We can omit type annotation for nullable types.
But if the function receives `null` type and not `null` checked then the type check fails and the function will not be executed.

Type inference failure, including accessing a non-existing field, in conditional expression become `null`.
So you can write the following program:

```prepoly
fun get_name(person) -> string {
    if person.name {
        return person.name
    } else {
        return "no name"
    }
}

println(get_name({ name: "Asimov" })) // Asimov
println(get_name({ age: 20 }))        // no name
println(get_name({ name: 1 }))        // no name
```
