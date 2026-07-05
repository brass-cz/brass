---
title: "LLM agents"
description: "A system prompt that teaches LLM agents to write valid prepoly."
---

prepoly is new enough that an LLM has not seen it during training, so an agent
will otherwise write code in the dialect of whatever language the syntax most
resembles. The text below is a self-contained system prompt that teaches the
language from scratch. Drop it into your agent's project instructions (for
example `AGENTS.md` or `CLAUDE.md`) so the agent writes valid prepoly.

````markdown
# Writing prepoly

You are writing **prepoly**, a statically type-checked, structurally typed
language with Hindley-Milner type inference. It looks like a scripting language
but every function is fully type-checked just before it runs. Source files use
the `.pp` extension. Do not assume any feature from another language exists
here; rely only on what is described below. After writing code, type-check it
with `prepoly check file.pp`.

## Mental model

- Most types are inferred; annotations are optional and used to constrain.
- An integer literal defaults to `int32` (`int64` when the value does not fit
  in 32 bits); a decimal literal defaults to `float64`. `len()` returns
  `int64`.
- Records and arrays have reference semantics; mutating through one binding is
  visible through every binding that shares the object.
- There are no explicit generic type parameters. Polymorphism comes from type
  inference and from structural typing (a function constrains a value only by
  the members it actually uses).

## Lexical rules

- Comments: `// line` and `/* block, which may nest */`.
- Newlines separate statements. A line continues onto the next when it ends
  with a binary operator, or when the next line begins with `.` (method chain).
- Commas between type fields/members and between match arms are optional;
  newlines work as separators too. Record literal fields still use commas when
  more than one field is written. Trailing commas are allowed.
- String interpolation: inside a string literal, `{expr}` evaluates `expr` and
  inserts its text, e.g. `"sum = {a + b}"`. Escapes like `\n`, `\t` work.
- `if` and `match` are expressions and yield a value.

## Declarations

```
const pi = 3.14159      // immutable binding; reassigning is a compile error
let total = 0           // mutable binding
total += 10
let [a, b] = [10, 20]   // array/tuple destructuring
```

## Functions

```
fun gcd(a, b) {              // unannotated params: inferred type and mutability
    if b == 0 { return a }
    return gcd(b, a % b)
}

fun area(s: Shape) -> float64 {   // optional param and return annotations
    return 0.0
}
```

- A function with no explicit return type has its return type inferred.
- `void` is the no-value return type.
- Top-level statements run top to bottom (functions and types may be used
  before their definitions; a top-level BINDING may not); `main` is called last
  if defined.

### References and mutability

- An UNANNOTATED parameter is a read-only reference when the body only reads
  it. If the body MUTATES it, the parameter becomes a PRIVATE DEEP COPY at
  entry: the function works on its own copy and the caller's value is
  untouched.
- Writing through to the caller requires the explicit `ref(mut(T))` form.
- `infer` is a read-only deep copy; mutating an `infer` parameter is a compile
  error. Use `infer[]` to require "an array, element type inferred".
- `self` is always a reference (mutating methods mutate the receiver).
- Closures capture their environment by mutable reference.

```
fun double(a) {            // mutated => a is a private deep copy
    for e in a { e *= 2 }
}
let arr = [1, 2, 3]
double(arr)                // arr is still [1, 2, 3]

fun double_through(a: ref(mut(int32[]))) {
    for e in a { e *= 2 }
}
double_through(arr)        // arr is now [2, 4, 6]
```

## Types

`type` defines both records and sum types. A type body holds fields and method
_signatures_ (interface requirements); a member written with `(params)` and no
body is a signature, one without parens is a field. Methods are implemented
OUTSIDE the type with `fun T.m(...)`, in the same module that declares `T`. A
method whose first parameter is `self` is an instance method (called
`value.method(...)`); otherwise it is a static method (called `Type.method(...)`).
`Self` inside a body refers to the type. A method is in scope wherever the type
is, with no separate import.

```
type Account = {
    owner: string
    balance: int32
}

fun Account.open(owner: string) -> Account {   // static method (no self)
    return Self { owner: owner, balance: 0 }
}
fun Account.deposit(self, amount: int32) {      // instance method
    self.balance += amount
}
fun Account.describe(self) -> string {
    return "{self.owner}: {self.balance}"
}

let acc = Account.open("Alice")
acc.deposit(100)
println(acc.describe())
```

A field without a type annotation accepts any value (its type is inferred per
construction site).

### Sum types (tagged unions)

```
type Shape =
    | Circle { radius: float64 }
    | Rectangle { width: float64, height: float64 }
    | Point                              // a variant may have no fields

let s = Shape.Circle { radius: 2.0 }     // construct as Type.Variant { ... }
```

Variants are nominal. A method on a sum type is implemented with `fun T.m(self)`
and applies to every variant (its body typically `match`es on `self`). Sum types
may be recursive (a variant field can be the type itself).

### Interfaces and structural subtyping

`type B: A` makes `B` satisfy interface `A`: it requires `B` to provide every
member of `A`, checked at compile time. No implementation is inherited. Multiple
interfaces: `type B: A, C`. This works for records and for every variant of a
sum type.

```
type Showable = { to_string(self) -> string }   // a method signature: a requirement

type User: Showable = {
    name: string
}

fun User.to_string(self) -> string { return self.name }
```

Separately, a plain function with an UNANNOTATED parameter accepts ANY value
that structurally has the members it uses -- no interface or inheritance needed:

```
fun print_info(obj) { println(obj.to_string()) }   // anything with to_string
```

## Pattern matching

`match` over a sum type is checked for exhaustiveness. Patterns include
variants with field bindings, literals, and `_` (wildcard). `if let` matches a
single variant (or a `T.from` result) and binds its fields.

```
fun describe(s: Shape) -> string {
    return match s {
        Circle { radius } => "circle r={radius}",
        Rectangle { width, height } => "rect {width}x{height}",
        Point => "a point",
    }
}

if let Circle { radius } = s {
    println("radius {radius}")
}

match n {
    0 => "zero",
    1 => "one",
    _ => "many",
}
```

## Nullable and Result

- `T?` is a nullable type. A nullable value must be narrowed before use with an
  `if` guard: inside `if x { ... }` (or after `if !x { return ... }`) the value
  `x` is narrowed from `T?` to `T`. Inside a conditional, an inference failure
  such as reading a nonexistent field becomes `null` rather than an error.
- `T!` is a `Result`. Construct an error with `error(x)`. A bare value returned
  where a `Result` is expected is automatically wrapped as `Ok`. The postfix
  `!` operator propagates: `expr!` unwraps `Ok` or returns the `Err` early from
  the enclosing function.
- The Result variants are `Ok { value }` and `Err { error }`; match on those
  field names.

```
fun parse_positive(s: string) {
    let n = int32.parse(s)!           // returns early on parse failure
    if n < 0 { error("negative: {n}")! }
    return n                          // implicitly wrapped in Ok
}

match parse_positive("42") {
    Ok { value } => println("got {value}"),
    Err { error } => println("failed: {error}"),
}

fun first_even(nums: int32[]) -> int32? {
    for n in nums { if n % 2 == 0 { return n } }
    return null
}
let x = first_even([1, 3, 4])
if x { println("first even {x}") }    // x is int32 inside the guard
```

## Anonymous records and structural conversion

`{ field: value, ... }` is an anonymous structural record. Calling a method on
it resolves structurally: if exactly ONE in-scope record type declares that
method and the value satisfies its fields, that type's method dispatches with
no annotation (`{ name: "A" }.display()` runs `Person.display`). In scope
means declared in or imported into the current module — an anonymous value
never adopts a type the module has not imported (a value already carrying a
nominal type, e.g. an imported function's return, dispatches methods without
importing the type name). Several satisfying types make the call ambiguous (a
compile error at the value asking for an annotation); a missing field is
reported at the value with the unsatisfied constraint. For a record type `T`, `T.from(v)` yields `T?`: the
record value when `v` structurally has all of `T`'s fields (decided at that
call site), else `null`. Pair it with `if let`:

```
fun get_name(obj) {
    if let person = Person.from(obj) {
        return person.display()
    } else {
        error("not a Person")!
    }
}
```

## Numbers, strings, conversions

- Primitive types: `int8/16/32/64`, `uint8/16/32/64`, `float32`, `float64`,
  `bool`, `string`, `void`. There is no separate char type; a character is a
  one-character `string`.
- Numeric operators and comparisons implicitly convert mixed numeric operands
  to their common type, but only VALUE-PRESERVING conversions are implicit
  (wider same-signed integer, unsigned into strictly wider signed, int into a
  float that holds it exactly, float32 into float64). Lossy pairs (`int64`
  with `uint64`, `int64` with `float64`, any narrowing) are compile errors;
  convert explicitly. `string.from(x)` always succeeds and returns
  `string`. `float64.from(int)` widens. `int32.from(x)` / `uint8.from(x)` and
  the `T.parse(s)` family can fail and return `T!`, so unwrap with `!` or
  `match`.

```
let n = int32.parse("123")!
let f = float64.from(n) + 0.5
let s = string.from(42)
let b = uint8.from(300)               // Err: out of range -> match or `!`
```

String offsets are UTF-8 byte offsets: `len` and `find` agree on byte
positions. There is no string slicing on the surface, and direct `s[i]` string
indexing is not part of the supported runtime surface; use `s.chars()` when you
need one-character strings, or `split`/`find`/`replace` for substring work.

## Collections and operators

- Arrays: `T[]` dynamic, `T[n]` fixed length, literal `[1, 2, 3]`, index
  `arr[i]`, append `arr.push(x)`, `arr.pop() -> T?`, `arr.insert(i, x)`,
  `arr.remove(i) -> T`. The length-changing methods are dynamic-array only.
  Tuples: `[T, U]`. Iterate with `for x in xs`; `[lo..hi]` is the half-open
  integer range as an array.
- Operators: arithmetic `+ - * / %`; comparison `== != < <= > >=`; logical
  `&& || !`; bitwise `& | ^ ~ << >>`; compound assignment `+= -= *= /= %=`.
  Equality is `==` (a single `=` is assignment).

## Closures and higher-order functions

```
let inc = (n: int32) -> n + 1                 // expression body
let acc = (amount: int32) -> {                // block body needs `return`
    total += amount
    return total
}
let f = () -> { println("no args") }
[3, 1, 4].filter((x) -> x > 1).map((x) -> x * 10).fold(0, (a, b) -> a + b)
```

A closure passed as a parameter is called as the local value even if its name
collides with a global function.

## Methods

Implement a method with `fun T.m(self, ...)` in the same module that declares
`T`, and call it as `recv.m(args)`. There is no UFCS: a plain free function is
NOT callable as `recv.f(...)`. The standard-library array/string helpers are
methods on those types (`arr.map(g)`, `s.split(",")`); the standard library may
add methods to primitive types, which user code cannot. Define your own the same
way:

```
type Vec2 = { x: float64, y: float64 }
fun Vec2.length_sq(self) -> float64 { return self.x * self.x + self.y * self.y }
let sq = v.length_sq()
```

## Compile-time reflection

`fields(x)` iterates a record's declared fields; it is legal only as a `for`
iterable and is unrolled per field. In the body the loop variable is the field
NAME (a string) except in `x[field]`, which projects the field's value. Use it
with an uninitialized `let ret: T` (an annotated `let` with no initializer) to
build a value field by field: storing into every field through the loop makes
`ret` fully initialized. `typeof(x)` names `x`'s static type -- a string in
value position (`print(typeof(x))`), a type in type position (`let y:
typeof(x)`), and a static receiver (`typeof(x).from(v)`). Both read only the type, so they are allowed on an uninitialized binding.

```
type Point = { x: int64, y: int64 }
fun doubled(p: Point) -> Point {
    let ret: Point
    for field in fields(ret) { ret[field] = p[field] * 2 }
    return ret
}
```

Mutually recursive functions are supported on the typed back end only when the
functions carry return-type annotations (each recursive call types against the
annotation).

## Modules

One file is one module; the directory layout is the module path
(`geometry/vec.pp` is the module `geometry.vec`). Import selected names with
`import path.{ A, B }`, one name with `import path.Name`, or the whole module
with `import path` -- its exports are then used qualified by the path's last
segment (`vec.dot(a, b)`, `vec.Vec2`, `vec.Shape.Circle { r: 1.0 }`).
`import path as name` overrides the qualifier. The path is relative to the
importing file. A name beginning with `_` is private to its module and cannot
be imported or accessed qualified.

```
import geometry.vec.{ Vec2, dot }
import geometry.vec.{ dot as vdot }
import geometry.vec.Vec2
import geometry.vec
import geometry.vec as g
```

## Standard library (implicit prelude, no import needed)

- IO: `print`, `println`, `input() -> string!` (one line, without the trailing
  newline; unwrap with `!` or `match`), `read_file(path) -> string!`,
  `write_file(path, content) -> void!`. Lower-level: `open`, `File.stdin/stdout`.
- Arrays: `map`, `filter`, `fold`, `each`, `slice(start, end)`, `reverse`,
  `contains`, `sort`, `len`, `push`, `pop`, `insert`, `remove`.
- Strings: `split`, `join`, `trim`, `starts_with`, `ends_with`, `find`,
  `replace`, `chars`, `to_upper`, `to_lower`, `len`.
- Math: `abs`, `min`, `max`, `sqrt`, `floor`, `ceil`, `pow`.
- Numeric limits: `INT32_MAX`, `INT32_MIN`, `INT64_MAX`, `INT64_MIN`.
  Free-function conversion aliases also exist (`int32_parse`, `int32_from`,
  `float64_parse`, `float64_from`, `string_from`), equivalent to the method
  forms above.
- Collections: `HashMap` (open-addressing hash map) is in a NESTED std module
  and needs an explicit `import std.collections.hashmap.{ HashMap }`.
  `let m = HashMap.new()` takes no arguments; the key/value types are inferred
  from the first `set` (so `let m = HashMap.new(); m.set("a", 1)` is a
  `string -> int32` map). Methods: `set(k, v)`, `get(k)` (nullable),
  `get_or(k, default)`, `contains_key(k)`, `delete(k)`, `size()`,
  `is_empty()`, `keys()`, `values()`, `pairs()`, `clear()`, and
  `HashMap.from_pairs([[k, v], ...])`.
- `assert(cond, msg?)` aborts when `cond` is false (`msg` is optional).
- Identifiers beginning with `_` (e.g. `_string_bytes`, `_panic`) are runtime
  internals -- do not call them directly; use the prelude wrappers above.
- File I/O and concurrency run on the native runtime; `prepoly repl` does not
  implement those runtime features.

## Concurrency (experimental -- avoid unless asked)

The only primitives are `spawn(f)` (run a closure on a thread), `with(c, f)`
(acquire a shared object to read/use it), and `sync()` (wait for spawned work
before observing its results). The compiler infers ownership automatically; you
never write move/freeze/cown. Spawned work is otherwise joined only at the end
of `main`, so insert `sync()` before a read that may race ahead.

## Common mistakes to avoid

- Implicit numeric conversion is value-preserving widening ONLY. Narrowing
  (smaller width, sign change, `float64 -> float32`, `int64 -> float64`,
  float -> int) always goes through `T.from(x)!`.
- `len()` returns `int64`; implicit int widening covers the common cases
  (`[0..len(xs)]` works without an annotation).
- Use `==` for equality, not `=`.
- A nullable (`T?`) value cannot be used until narrowed by an `if` guard.
- Match `Result` with the field names `Ok { value }` / `Err { error }`.
- Construct sum-type values as `Type.Variant { ... }`, and call static methods
  as `Type.method(...)`.
- Block-bodied closures and functions need an explicit `return`; expression
  bodies (`(x) -> x + 1`) do not.
- The `!` error-propagation operator works only inside a function or closure
  body — top-level code cannot use `expr!`; wrap the code in `fun main()`.

## Worked example

```
type Shape =
    | Circle { radius: float64 }
    | Rectangle { width: float64, height: float64 }

fun area(s: Shape) -> float64 {
    return match s {
        Circle { radius } => 3.14159 * radius * radius,
        Rectangle { width, height } => width * height,
    }
}

fun main() {
    let shapes = [
        Shape.Circle { radius: 2.0 },
        Shape.Rectangle { width: 3.0, height: 4.0 },
    ]
    let total = shapes.map((s) -> area(s)).fold(0.0, (a, b) -> a + b)
    println("total area = {total}")
}
```
````
