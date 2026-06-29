# Type system

prepoly utilizes **type inference**, so in most cases we don't need to write type annotations even though the program is statically typed.
Here, let's see an overview of prepoly's type system.

## Primitives and special types

- The default type of an integer literal (e.g. `1`) is `int32`, and the default type of a decimal literal (e.g. `1.0`) is `float64`
- The type of text is `string`
- A static array of type `T` with length `n` is represented by `T[n]`
- A dynamic array of type `T` is represented by `T[]`
- A tuple type is represented by `[T, U, ...]`

Also, prepoly uses the following special type annotations:

- A reference to type `T` is written as `ref(T)`
- A mutable reference to type `T` is written as `ref(mut(T))`

The type of an argument is treated as a reference type if we don't write any type annotation.
The mutability of a function argument is inferred:

```prepoly
fun double(a) { // a: ref(mut(int32))
    for e in a {
        e *= 2
    }
}

let arr = [1, 2, 3]
double(arr)
println(arr) // outputs [2, 4, 6]
```

We can use the `infer` type annotation to explicitly infer a specific part of the type:

```prepoly
fun print_all(a: infer[]) {
    for e in a {
        println(e)
    }
}

print_all(["a", "b", "c"])
```

Note that the `infer` annotation does not include `ref` or `mut`.
So a value annotated with `infer` is deeply copied:

```prepoly
fun double(a: infer) {
    for e in a {
        e *= 2
    }
    println(a)
}

const arr = [1, 2, 3]
double(arr)  // outputs [2, 4, 6]
println(arr) // outputs [1, 2, 3]
```

## Defining types

We can define new types with their fields and methods as follows:

```prepoly
type Person = {
    first_name: string,
    last_name: string,
    display(self) {
        return "{self.first_name} {self.last_name}"
    },
}

fun main() {
    const newton = Person {
        first_name: "Isac",
        last_name: "Newton",
    }
    println("{newton.display()}")
}
```

This program outputs `Isac Newton`.

We can define "OR" types:

```prepoly
type DegreeProgram =
    | Bachelor {
        year: int32,
    }
    | Master {
        year: int32,
    }
    | Doctor {
        year: int32,
    }
```

Using `DegreeProgram` type, we can define `Student` type:

```prepoly
type Student: Person = {
    first_name,
    last_name,
    display(self) {
        return "{self.id}: {self.first_name} {self.last_name}"
    },
    id,
    program: DegreeProgram,
}
```

Here, we wrote the `Person` type on the left of `Student`.
This requires that the `Student` type include all fields of the `Person` type.

Using these definitions, let's write a complete program.
Here we enhance `display` with a `match` expression that formats each `DegreeProgram` variant:

```prepoly
type Person = {
    first_name: string,
    last_name: string,
    display(self) {
        return "{self.first_name} {self.last_name}"
    },
}
type DegreeProgram =
    | Bachelor {
        year: int32,
    }
    | Master {
        year: int32,
    }
    | Doctor {
        year: int32,
    }
type Student: Person = {
    first_name,
    last_name,
    display(self) {
        const program = match self.program {
            Bachelor { year } => "Bachelor {year}",
            Master { year } => "Master {year}",
            Doctor { year } => "Doctor {year}",
        }
        return "{self.id} ({program}): {self.first_name} {self.last_name}"
    },
    id,
    program: DegreeProgram,
}

fun main() {
    const newton = Student {
        first_name: "Isac",
        last_name: "Newton",
        id: 1001,
        program: DegreeProgram.Master { year: 1 },
    }
    println("{newton.display()}")
    println("{newton}")
}
```

Executing this shows the following output:

```
1001 (Master 1): Isac Newton
Student {
    first_name: Isac,
    last_name: Newton,
    id: 1001,
    program: DegreeProgram.Master {
        year: 1,
    },
}
```

In the above example, we didn't write any type annotation for `Student.id`.
So we can write a string as the value of `Student.id`:

```prepoly
const edison = Student {
    first_name: "Thomas",
    last_name: "Edison",
    id: "AL17001",
    program: DegreeProgram.Doctor { year: 3 },
}
println("{edison.display()}")
```

This program can be placed alongside the above `newton` example, and the output is as follows:

```
AL17001 (Doctor 3): Thomas Edison
```

We can use `Person` type if we would like to define a function which receives `Person` and its derivative:

```prepoly
fun print_name(person: Person) {
    println(person.display())
}
print_name(edison)
```

## `null` and `Result`

prepoly has a `null` type and a `Result` type.

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

The variable `a` of the function `double` has the type `int32?`.
The `?` means that the value may be `null`.
A value that may be `null` must be checked with an `if` expression.

Calling the `error` function makes the return value a `Result.Err`.
When a function returns a plain value where a `Result` is expected, it is wrapped as `Result.Ok`.
A `Result` type that holds an `int32` value is denoted as `int32!`.

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

In a conditional expression, a type inference failure, such as accessing a non-existent field, becomes `null`.
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
