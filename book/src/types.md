# Types and methods

## Record types

We can define new types with their fields as follows:

```prepoly
type Account = {
    owner: string
    balance: int32
}
```

Methods are implemented outside the type with `fun T.m(...)`, in the same
module that declares the type. A method whose first parameter is `self` is an
instance method (called as `value.method(...)`); one without is a static
method (called as `Type.method(...)`). `Self` inside a body refers to the
type.

```prepoly
// A static method has no `self` parameter.
fun Account.open(owner: string) -> Account {
    return Self { owner: owner, balance: 0 }
}

// Instance methods take `self` first.
fun Account.deposit(self, amount: int32) {
    self.balance += amount
}

fun Account.describe(self) -> string {
    return "{self.owner}: {self.balance}"
}

fun main() {
    let acc = Account.open("Alice")
    acc.deposit(100)
    acc.deposit(50)
    println(acc.describe())   // Alice: 150
}
```

Records have reference semantics: `acc.deposit(100)` mutates the account the
caller sees, because `self` is always a reference. A method is in scope
wherever the type is, with no separate import.

Method return types are inferred like function return types, so `Account.open`
could omit its `-> Account` annotation.

## Fields without a type

A field may omit its type annotation. Such a field accepts any value, and its
type is inferred per construction site:

```prepoly
type Student = {
    name: string
    id
}

let a = Student { name: "Newton", id: 1001 }
let b = Student { name: "Edison", id: "AL17001" }
println("{a.id} / {b.id}")   // 1001 / AL17001
```

## Sum types

The same `type` keyword defines "OR" types (tagged unions). Variants are
written with `|`, and each variant may carry fields — or none:

```prepoly
type Shape =
    | Circle { radius: float64 }
    | Rectangle { width: float64, height: float64 }
    | Point
```

Construct a variant as `Type.Variant { ... }` (a unit variant is just
`Type.Variant`), and take values apart with `match` — see
[Pattern matching](pattern-matching.md):

```prepoly
fun area(s: Shape) -> float64 {
    return match s {
        Circle { radius } => 3.14159 * radius * radius,
        Rectangle { width, height } => width * height,
        Point => 0.0,
    }
}

println(area(Shape.Circle { radius: 2.0 }))   // 12.56636
```

A sum type may be recursive: a variant field can be the type itself. This
expression tree evaluates `1 + 2 * 3`:

```prepoly
type Expr =
    | Num { value: int32 }
    | BinOp { op: string, left: Expr, right: Expr }

fun eval(e: Expr) -> int32 {
    return match e {
        Num { value } => value,
        BinOp { op, left, right } => {
            let l = eval(left)
            let r = eval(right)
            match op {
                "+" => l + r,
                "*" => l * r,
                _ => 0,
            }
        },
    }
}

let expr = Expr.BinOp {
    op: "+",
    left: Expr.Num { value: 1 },
    right: Expr.BinOp {
        op: "*",
        left: Expr.Num { value: 2 },
        right: Expr.Num { value: 3 },
    },
}
println("result = {eval(expr)}")   // result = 7
```

## Interfaces

A type whose body contains method *signatures* (a member with parameters but
no body) acts as an interface. Writing `type B: A = ...` requires `B` to
provide every member of `A`, checked at compile time. No implementation is
inherited:

```prepoly
type Showable = {
    to_string(self) -> string
}

type User: Showable = {
    name: string
    age: int32
}

fun User.to_string(self) -> string {
    return "{self.name} (age {self.age})"
}
```

Multiple interfaces are comma-separated: `type User: Showable, Comparable`.
An interface may also require plain fields, and it works for sum types too —
every variant must satisfy it:

```prepoly
type Named = {
    name: string
}

type Pet: Named =
    | Cat { name: string, indoor: bool }
    | Dog { name: string, breed: string }
```

## Structural subtyping

Separately from interfaces, a plain function with an unannotated parameter
accepts *any* value that structurally has the members it uses — no interface
declaration needed:

```prepoly
type ConsoleLogger = {
    prefix: string
}

fun ConsoleLogger.log(self, msg: string) {
    println("[{self.prefix}] {msg}")
}

type TaggedLogger = {
    prefix: string
    tag: string
}

fun TaggedLogger.log(self, msg: string) {
    println("[{self.prefix}/{self.tag}] {msg}")
}

// No constraint on `logger` other than "has a log method".
fun run_with(logger, task: string) {
    logger.log("starting {task}")
    logger.log("done {task}")
}

run_with(ConsoleLogger { prefix: "APP" }, "task1")
run_with(TaggedLogger { prefix: "APP", tag: "net" }, "task2")
```

```
[APP] starting task1
[APP] done task1
[APP/net] starting task2
[APP/net] done task2
```

## Anonymous records

`{ field: value, ... }` is an anonymous structural record. When exactly one
in-scope record type declares a method and the anonymous value satisfies that
type's fields, the method is callable directly:

```prepoly
type Person = {
    name: string
}

fun Person.display(self) {
    println("I am {self.name}")
}

let someone = { name: "Asimov" }
someone.display()   // I am Asimov
```

You can also convert a value to a record type explicitly with `T.from(v)`,
which yields `T?` — the record when `v` structurally has all of `T`'s fields,
else `null`:

```prepoly
fun get_name(obj) {
    if let person = Person.from(obj) {
        person.display()
    } else {
        println("not a Person")
    }
}

get_name({ name: "Yukawa", age: 42 })   // I am Yukawa
get_name({ age: 42 })                   // not a Person
```

The precise rules for method resolution, ambiguity, and record coercion are in
the [type system reference](references/types.md#records-and-structural-typing).
