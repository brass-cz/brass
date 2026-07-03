# Type system

prepoly utilizes **type inference**, so in most cases we don't need to write type annotations even though the program is statically typed.
Here, let's see an overview of prepoly's type system.

## Primitives and special types

- The default type of an integer literal (e.g. `1`) is `int32` when the value fits, otherwise `int64` (so `9223372036854775807` is an `int64`); the default type of a decimal literal (e.g. `1.0`) is `float64`
- The type of text is `string`
- A static array of type `T` with length `n` is represented by `T[n]`
- A dynamic array of type `T` is represented by `T[]`
- A tuple type is represented by `[T, U, ...]`

A bracket literal `[...]` is typed in this order:

1. A type annotation (or another inference result, such as the parameter it is passed to) decides: the literal takes that type.
2. Elements that cannot unify make it a tuple -- but a `null` element never does: `null` unifies with any element type, so `[4, null, 65]` is a sequence of `int32?`.
3. Bound immutably (`const`), it is a fixed-length array: `const a = [1, 2, 3]` is `int32[3]`.
4. Bound mutably (`let`) or in any other position, it is a growable array: `let a = [1, 2, 3]` is `int32[]`.

A fixed-length array is usable where a dynamic array of the same element is required (the length is extra static information), but not the reverse.

An arithmetic or comparison operator between two numeric values of different types implicitly converts both operands to a common type: integers widen to the wider width (mixing signed and unsigned yields a signed integer), and an integer combined with a float becomes that float.
So `int32 + int64` is `int64` and `int32 + float64` is `float64`.

Numeric values also convert automatically when they *flow* into a numeric position of another type -- an assignment, an argument, a return value, a compound assignment, or an element/field store. Any integer converts to any integer type (a narrowing conversion is allowed and may be lossy), a float to a float of any width, and an integer to a float: `let b: int64 = an_int32` and `total += an_int32` (with `total: int64`) both widen the value. The one exception is float to int, which would silently drop the fraction; convert explicitly with `int32.from(x)`.

Also, prepoly uses the following annotations for how an argument is passed:

- `ref(T)` -- an immutable reference: the callee borrows the value and may read it but not mutate it.
- `ref(mut(T))` -- a mutable reference: the callee may mutate the value in place, and the change is visible to the caller.
- `mut(T)` -- a mutable deep copy: the callee gets its own copy to mutate; the caller's value is unchanged.

When a non-numeric argument has no annotation, its passing mode is inferred from how the body uses it.
A parameter the body only reads is a shared reference (`ref`); one the body mutates is a private deep copy (`mut`), so the mutation stays local and does not reach the caller:

```prepoly
fun double(a) { // a: mut(int32[]) -- mutated, so a private copy
    for e in a {
        e *= 2
    }
}

let arr = [1, 2, 3]
double(arr)
println(arr) // outputs [1, 2, 3]: `double` doubled its own copy
```

To mutate the caller's value through a function, annotate the parameter `ref(mut(T))` -- a mutable reference writes through:

```prepoly
fun double(a: ref(mut(int32[]))) {
    for e in a {
        e *= 2
    }
}

let arr = [1, 2, 3]
double(arr)
println(arr) // outputs [2, 4, 6]
```

A numeric argument (e.g. `int32`) is always passed by value, so it is never a reference.

The `self` receiver of a method is a special case: it is always a reference.
A method that only reads `self` receives `ref(Self)`; one that mutates it receives `ref(mut(Self))`, so the change is visible to the caller.
To work on an owned copy of `self` instead, annotate it `self: Self`.

We can use the `infer` type annotation to explicitly infer a specific part of the type:

```prepoly
fun print_all(a: infer[]) {
    for e in a {
        println(e)
    }
}

print_all(["a", "b", "c"])
```

The `infer` annotation implies neither `ref` nor `mut`: a value annotated with `infer` is a read-only deep copy, so mutating it is an error.

```prepoly
fun total(a: infer) -> int32 {
    let sum = 0
    for e in a {
        sum += e
    }
    return sum
}

const arr = [1, 2, 3]
println(total(arr)) // outputs 6; `a` is a read-only copy
```

## Defining types

We can define new types with their fields as follows:

```prepoly
type Person = {
    first_name: string,
    last_name: string,
}
```

Methods are implemented outside the type with `fun T.m(...)`, in the same module
that declares the type. A method whose first parameter is `self` is an instance
method (called as `value.method(...)`); one without is a static method (called as
`Type.method(...)`). `Self` inside a body refers to the type. A method is in
scope wherever the type is, with no separate import.

```prepoly
fun Person.display(self) {
    return "{self.first_name} {self.last_name}"
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
    id,
    program: DegreeProgram,
}

fun Student.display(self) {
    return "{self.id}: {self.first_name} {self.last_name}"
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
}
fun Person.display(self) {
    return "{self.first_name} {self.last_name}"
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
    id,
    program: DegreeProgram,
}
fun Student.display(self) {
    const program = match self.program {
        Bachelor { year } => "Bachelor {year}",
        Master { year } => "Master {year}",
        Doctor { year } => "Doctor {year}",
    }
    return "{self.id} ({program}): {self.first_name} {self.last_name}"
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
    first_name: "Isac",
    last_name: "Newton",
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

## `anonymous` structure

Anonymous structure can be written as `{ field: value, ... }`.
You can access its fields by null checking or type conversion using `T.from()`:

```prepoly
fun get_name(obj) {
    if let person = Person.from(obj) {
        return person.display()
    } else {
        error("not a Person type!")!
    }
}

// Result.Ok { value: Hideki Yukawa }
println(
    get_name({
        first_name: "Hideki",
        last_name: "Yukawa"
    })
)
// Result.Err { error: not a Person type! }
println(get_name({ last_name: "Yukawa" }))
```
