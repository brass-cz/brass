---
title: "Types and methods"
description: "Records, methods, sum types, interfaces, and structural subtyping by example."
---

## Record types

New types are defined with their fields:

```brass
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

```brass
type Account = {
    owner: string
    balance: int32
}

// A static method has no `self` parameter.
fun Account.open(owner) -> Account {
    return Self { owner: owner, balance: 0 }
}

// Instance methods take `self` first.
fun Account.deposit(self, amount) {
    self.balance += amount
}

fun Account.describe(self) {
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

Method parameter and return types are inferred like function ones. `deposit`
and `describe` above carry no annotations at all, and `Account.open` could
omit its `-> Account` too.

## Fields without a type

A field may omit its type annotation. Such a field accepts any value, and its
type is inferred per construction site:

```brass
type Student = {
    name: string
    id
}

let a = Student { name: "Newton", id: 1001 }
let b = Student { name: "Edison", id: "AL17001" }
println("{a.id} / {b.id}")   // 1001 / AL17001
```

## Type slots

An unannotated field takes whatever type its construction site provides, but
it has no name that other fields can refer to. A record can instead name its
type parameters as **type slots** — members declared with the `type` keyword —
and express other fields over them with `Self.<slot>`. A slot has no runtime
storage: it never appears in the layout or in a construction literal, it only
names a type:

```brass
type Stack = {
    type item
    items: Self.item[]
}

fun Stack.new() {
    return Self { items: [] }
}

fun Stack.add(self, v) {
    self.items.push(v)
}

fun Stack.top(self) {
    return self.items[len(self.items) - 1]
}

fun main() {
    let s = Stack.new()
    s.add(10)
    s.add(20)
    println(s.top())   // 20
}
```

`Stack.new()` needs no sample value: `item` starts open, the first `add`
fixes it to `int32`, and a later `s.add("oops")` is a compile error rather
than a runtime surprise.

A **refinement** `Base { slot: T, ... }` pins slots up front. Written as the
right-hand side of a `type` declaration it names that concrete instance — an
alias, not a new type:

```brass
type Stack = {
    type item
    items: Self.item[]
}

fun Stack.new() {
    return Self { items: [] }
}

fun Stack.add(self, v) {
    self.items.push(v)
}

type Names = Stack { item: string }

fun greet(s: Names) {
    for name in s.items {
        println("hello, {name}")
    }
}

fun main() {
    let s: Names = Stack.new()
    s.add("Ada")
    s.add("Grace")
    greet(s)
}
```

Annotating the binding `let s: Names` pins `item` to `string` before anything
is stored, and `greet` accepts any stack whose `item` is `string`: the alias
unifies with a matching instance instead of demanding a distinct nominal
type. The prelude's `HashMap` is built exactly this way — `key` and `value`
slots, pinned by the first stored pair or by an alias such as
`type Counts = HashMap { key: string, value: int64 }`.

Slots, refinements, and their exact rules are in the
[type system reference](/references/types/#type-slots-and-refinements).

## Sum types

The same `type` keyword defines "OR" types (tagged unions). Variants are
written with `|`, and each variant may carry fields, or none:

```brass
type Shape =
    | Circle { radius: float64 }
    | Rectangle { width: float64, height: float64 }
    | Point
```

Construct a variant as `Type.Variant { ... }` (a unit variant is just
`Type.Variant`), and take values apart with `match`. See
[Pattern matching](/guides/pattern-matching/):

```brass
type Shape =
    | Circle { radius: float64 }
    | Rectangle { width: float64, height: float64 }
    | Point

fun area(s) {
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

```brass
type Expr =
    | Num { value: int32 }
    | BinOp { op: string, left: Expr, right: Expr }

fun eval(e) {
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

A type whose body contains method _signatures_ (a member with parameters but
no body) acts as an interface. Writing `type B: A = ...` requires `B` to
provide every member of `A`, checked at compile time. No implementation is
inherited:

```brass
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
An interface may also require plain fields; it works for sum types too,
where every variant must satisfy it:

```brass
type Named = {
    name: string
}

type Pet: Named =
    | Cat { name: string, indoor: bool }
    | Dog { name: string, breed: string }
```

## Structural subtyping

Separately from interfaces, a plain function with an unannotated parameter
accepts _any_ value that structurally has the members it uses, with no
interface declaration needed:

```brass
type ConsoleLogger = {
    prefix: string
}

fun ConsoleLogger.log(self, msg) {
    println("[{self.prefix}] {msg}")
}

type TaggedLogger = {
    prefix: string
    tag: string
}

fun TaggedLogger.log(self, msg) {
    println("[{self.prefix}/{self.tag}] {msg}")
}

// No constraint on `logger` other than "has a log method".
fun run_with(logger, task) {
    logger.log("starting {task}")
    logger.log("done {task}")
}

run_with(ConsoleLogger { prefix: "APP" }, "task1")
run_with(TaggedLogger { prefix: "APP", tag: "net" }, "task2")
```

## Anonymous records

`{ field: value, ... }` is an anonymous structural record. When exactly one
in-scope record type declares a method and the anonymous value satisfies that
type's fields, the method is callable directly:

```brass
type Person = {
    name: string
}

fun Person.display(self) {
    println("I am {self.name}")
}

let someone = { name: "Asimov" }
someone.display()   // I am Asimov
```

"In scope" is per module: an anonymous value only adopts a type declared in
or imported into the module where the call appears. If `Person` lives in
another module this one never imports, `someone.display()` is an error naming
the missing import. A `Person` returned by an imported function still
dispatches `display()`, though, because its type is already known.

You can also convert a value to a record type explicitly with `T.from(v)`,
which yields `T?`, the record when `v` structurally has all of `T`'s fields,
else `null`:

```brass
type Person = {
    name: string
}

fun Person.display(self) {
    println("I am {self.name}")
}

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
the [type system reference](/references/types/#records-and-structural-typing).
