---
title: "LLM agents"
description: "A compact, self-contained prompt for agents that write Brass."
---

Brass is unlikely to be present in a model's training data. Give the prompt
below to an agent before asking it to write `.cz` files. It covers every major
language and library area, but keeps each API to an overview; the reference
pages remain authoritative for exact signatures and edge cases.

````markdown
# Writing Brass

You are writing **Brass**, a statically typed, structurally typed scripting
language with flexible type inference. Source files use `.cz`. Do not import
syntax from Rust, TypeScript, Python, or another language unless it is listed
here.

Always validate generated code with:

```bash
brass check file.cz
```

A normal `brass file.cz` run checks the functions it needs and may leave
unused function bodies unchecked for that run. Declaration and signature
errors still prevent execution. Called methods follow the same body rules as
free functions: a rejected body, including an untaken branch, cannot execute,
and errors retain `brass check`'s diagnostic text and source locations.
Pattern contracts (irrefutable `let`/`const`/`for`, unique bindings, and
reachable match arms) follow the same body rules, including in closures and
each concrete generic instance. Module initializers are always checked.
Uninstantiated reflective method templates and statically pruned branches
follow the ordinary checker selection rules.
Checker warnings are non-fatal. `brass check` checks own-package items
completely, including unused functions. Dependencies are checked only where
reached or required for shared inference, in every mode. Unreached dependency
bodies produce no diagnostics, including recoverable body syntax errors;
errors that hide declaration boundaries remain errors.

## Syntax essentials

- Bindings are `const name = value` or mutable `let name = value`.
- Comments are `//`, `#`, and nestable `/* ... */`. A leading shebang is a
  `#` comment. `/** ... */` directly above a `fun` or `type` is a doc comment.
- Each statement, declaration, and import requires a newline, its enclosing
  block's `}`, or end of file. Semicolons are not separators. A line continues
  after a binary or assignment operator, before a leading `.`, or before `else`.
  Type members, refinement entries, and match arms require commas or newlines.
  Every comma-separated list allows a trailing comma, including interface lists
  and the `..` at the end of a record pattern.
- Numeric literals cannot touch an unconsumed letter, digit, or `_`:
  `0b12`, `0o78`, and `0xFFg` are errors. Exponents require digits after
  the optional sign (`1e` is an error). `_` separators are allowed, and
  leading-zero integers such as `0755` are decimal.
- String text cannot contain raw newlines; use `\n`. Interpolation
  expressions may span lines. Nested strings follow the same rules and
  support their own interpolations.
- Strings use escapes and `{expression}` interpolation. Escape a literal
  opening brace as `\{`.
- Equality is `==`; `=` is assignment. Compound assignments include `+=`,
  `-=`, `*=`, `/=`, and `%=`.
- `if` and `match` are expressions. Written as statements they have no
  value, so their arms need not agree in type. Loops are `while condition`
  and `for item in iterable`; `break` and `continue` are supported.
- Closures are `(x) -> expression` or `(x) -> { return value }`; multiple
  statements in a block need newlines. `return` requires a function or closure.
- `_` parameters are anonymous and may repeat; `_` is never a readable value.
  `self` is allowed only as the first parameter of a method or method signature.
- Functions and types may be used before their definitions. Top-level
  bindings initialize in textual order and may not be read early.
- Top-level statements run in module dependency order; `main()` runs last if
  present.

```brass
const greeting = "hello"
let count = 0
count += 1

fun twice(x: int32) -> int32 {
    return x * 2
}

const values = [1, 2, 3].map((x) -> twice(x))
println("{greeting}: {values}")
```

## Values and types

- Primitive types are `int8/16/32/64`, `uint8/16/32/64`, `float32`,
  `float64`, `bool`, `string`, and `void`. There is no character type; one
  character is a `string`.
- A numeric literal next to a typed operand takes that operand's type when it
  fits, so `uint8` arithmetic with a literal stays `uint8` and wraps. An
  integer literal with nothing to adapt to is `int32` if it fits, else
  `int64`, else `uint64`; a float literal is `float64`. Float literals must
  remain finite at their selected width: `1e400` is invalid, as is `1e39` in
  a `float32` context. Rounding (such as `0.1`) and underflow to zero remain
  valid. `len` returns `int64`.
- `T[]` is a growable array, `T[n]` a fixed-length array, `[T, U]` a tuple,
  and `[lo..hi]` a half-open integer range. Literal elements that join as
  numbers make an array (`[1, 2.5]` is `float64[]`), not a tuple.
- `T?` is nullable. Narrow it with `if value`, `if !value { return ... }`, or
  `if let` before using it as `T`. Only variables narrow: bind a field first
  (`if let next = node.next { ... }`).
- `T!` is a fallible Result. See Error handling below.
- Most annotations are optional. An annotation constrains inference; it does
  not opt into type safety.
- Numeric conversions are implicit only when value-preserving. Use
  `T.from(value)!` for checked narrowing or sign changes, `T.parse(text)!` for
  parsing, and `string.from(value)` for text.
- Arrays and records are reference values. Assignment can share them.

## Functions, parameters, and closures

```brass
fun distance(x: float64, y: float64) -> float64 {
    return sqrt(x * x + y * y)
}

fun double(x) {
    return x + x
}

println(double(2))     // 4
println(double(2.5))   // 5.0
```

- Return types are inferred when omitted. `void` means no value.
- An unannotated function is generic: each call site checks the body against
  its own argument types, so `double` above serves `int32` and `float64`
  alike.
- An unannotated parameter that is only read is passed by shared reference.
  If its body mutates the parameter, the callee receives a private deep copy.
- Use `ref(T)` for an explicit immutable reference and `ref(mut(T))` when the
  callee must mutate the caller's value. `mut(T)` is an explicit mutable copy.
  These three forms are whole parameter annotations only, including closure,
  method-signature, and function-type parameters. `T` contains no `ref`/`mut`;
  never put them in returns, fields, variable annotations, type arguments,
  array elements, or nullable/fallible wrappers.
- `infer` is a read-only copied value whose type is inferred; `infer[]`
  requires an array with an inferred element type.
- `self` is a reference, so instance methods can mutate their receiver.
- Closures capture live bindings by reference and may mutate them.
- A closure literal bound by `let`/`const` with an unannotated parameter is
  generic: each use instantiates it afresh. Any other closure value (a
  parameter, an argument, a field) is fixed by its first call.
- Closures may be fallible: a body using `error(...)` or a Result-operand `!`
  returns `Result<T, E>` (no `!` sugar on closure types); the caller unwraps
  with `!` or a `match`. `spawn` still requires a `void`-returning closure.
- Recursion, mutual recursion included, needs no annotations unless every
  value a function returns comes from the recursion; the checker then asks
  for a return type. A recursive call at a growing type (`f([x])` inside
  `f(x)`) is rejected.

## Records, methods, sums, and interfaces

Record fields live inside `type`; method implementations live outside it.
Sum variant names are plain undotted identifiers, never `Self` or keywords.

An instance method has `self` first. A method without `self` is static.
A method signature or implementation cannot share a name with a field of its
record or any variant of its sum. Anonymous record literals, anonymous record
types, and refinement lists cannot repeat a field name.

```brass
type Account = {
    owner: string
    balance: int64
}

fun Account.new(owner: string) -> Account {
    return Self { owner, balance: 0 }
}

fun Account.deposit(self, amount: int64) {
    self.balance += amount
}

type Stack = {
    type item          // a type slot: a named type parameter, no storage
    items: Self.item[]
}

type Names = Stack { item: string }   // alias pinning the slot
```

- Construct a record as `Type { field: value, ... }`; a bare `field` is
  shorthand for `field: field` (also in `{ ... }` and variant literals).
  Prefer the shorthand whenever the value is the same-named binding.
- Call methods as `value.method()` or `Type.static_method()`. There is no
  UFCS. `(value.field)(args)` calls a closure-valued field without an implicit
  receiver. A parenthesized method callee is rejected; method members are
  presence descriptors, not callable function values.
- A member written as `name(params) -> Return` inside a type is a required
  method signature, not stored data.
- Sum types use `type Name = Variant { fields } | Empty`. Construct a value
  as `Name.Variant { ... }` and match it as `Variant { ... }`.
- A match on a sum must cover every variant or use `_`; on a nullable sum it
  also needs a `null` or `_` arm.
- `type Child: Parent` declares structural conformance. Fields and complete
  method signatures are checked, including parameter passing modes,
  contravariant parameter compatibility, and return types; implementations
  are not inherited. Multiple parents are allowed.
- An unannotated function parameter is structural without an explicit
  interface: only the fields and methods used by the body are required.
- Structural subtyping (a record with more fields where fewer are required)
  applies to function and method parameters only. An annotated binding,
  return, field, array element, sum payload, map entry, or function-typed
  value needs exactly the declared record; an anonymous literal with exactly
  its fields is built as it, anything else converts with `T.from(v)`.
- `{ field: value }` is an anonymous record. It can dispatch to exactly one
  in-scope nominal record whose fields and requested method fit.
- `T.from(value) -> T?` performs structural conversion to record type `T`,
  unless `T` declares its own static `from`, which is called instead.
- `type name` inside a record declares a type slot: a type parameter other
  fields reference as `Self.name`. A slot is not stored and never appears in
  a construction literal; an open slot is fixed by the first value stored.
- A refined alias such as `type Names = Stack { item: string }` or
  `type Counts = HashMap { key: string, value: int64 }` pins type slots
  without creating a new nominal type. Import `std.collections.{ HashMap }`
  before using the map alias.

## Control flow and patterns

```brass norun
fun describe(shape: Shape) -> string {
    return match shape {
        Circle { radius } => "circle {radius}",
        Rectangle { width, height } => "{width}x{height}",
    }
}

if let Ok { value } = int32.parse("42") {
    println(value)
}
```

Patterns include variant patterns, record and array destructuring, literals,
bindings, and `_`. `if let pattern = value` selects one pattern. A conditional
can also probe structural member presence: `if value.method { ... }` asks at
compile time whether that type provides the member.

- `let`, `const`, and `for` require irrefutable patterns, recursively. Use
  bindings, `_`, plain records, or braced variants of a singleton sum. Literals,
  unit-variant names, and multi-variant destructures require `if let` or `match`.
- Tuple/fixed-array destructures require matching arity. A growable array
  requires a matching-length literal initializer for declaration destructuring.
- A name cannot be bound twice within one pattern, including nested fields.
- String patterns cannot contain interpolation.
- An arm after an irrefutable match arm is an error. Bare names bind variables;
  they do not compare with constants. Qualify unit variants to avoid typos
  becoming catch-all bindings.

`if value: Type { ... } else ...` is a compile-time type test, decided per
call site of the enclosing generic function. The subject must be one postfix
expression; group binary/prefix expressions, as in `if (a == b): bool`.
Negate with `if !(value: Type)` (parentheses required), never `if !value: Type`.
Tests are complete `if`/`else if` heads only, not values or logical operands.
A negated test swaps the matching and nonmatching arms; `infer` holes are
pinned by its `else` arm, where the test holds. Only the selected arm is checked
and compiled. Matching accepts the exact type or a subtype (structural record
satisfaction, declared sum parents); it never converts (`int32` fails an
`int64` test, `T` fails a `T?` test). `infer` in the tested type is a hole:
pinned by what the arm itself requires, otherwise matching anything
(`infer[]` = any array). Inside the arm the value keeps its own type.
Unselected paths contribute nothing to an instance: each instance's return
type comes from its live path alone, and an `error(...)` on a pruned path
does not make that instance return a Result.

```brass
fun length(val) {
    const bytes = if val: infer {          // string: to_bytes pins the hole
        to_bytes(val)
    } else if val: uint8[] {
        val
    } else if val: infer[] {
        val
    } else {
        return error("unsupported")
    }
    return bytes.len()
}
```

## Error handling

- Same-named types in different modules have distinct identities. A user type
  named `Location`, `Error`, or `Frame` does not replace the prelude types used
  in error traces. Only a trailing prelude `Location` parameter is implicit.
  A module's own `type Result` still supplies that module's fallibility sugar.
- `Result` has `Ok { value }` and `Err { error }` variants. Standard failures
  carry an `Error` record with `value`, `location`, `frames`, and `display()`.
- `error(payload)` creates an `Err`. Returning a plain value from a fallible
  function wraps it as `Ok`.
- `result!` unwraps `Ok` or returns the `Err` from the enclosing named
  function. `nullable!` unwraps a value or returns `null` early. Mixing those
  propagation kinds in an unannotated callable warns because it creates
  `Result<T, E>?`.
- `result.context(message)` adds trace context only on failure.
- `nullable.context(message)` converts absence into a traced error: `T?`
  becomes `T!`, while `Result<T, E>?` flattens to `Result<T, E>` instead of
  nesting Results. Use it when null and error should be one failure channel.
- At top level or in `main`, an unhandled `!` prints the error and exits
  non-zero.
- When matching a standard error, inspect `error.value`; interpolating
  `{error}` renders through `Error`'s `display` (the trace form). Use
  `{error.debug()}` for the raw record representation.

```brass
fun load_number(text: string) -> int32! {
    const value = int32.parse(text).context("reading number")!
    if value < 0 { return error("negative value") }
    return value
}

match load_number("12") {
    Ok { value } => println(value),
    Err { error } => println(error.display()),
}
```

## Collections and strings

- Growable arrays mutate with `push`, `pop`, `insert`, and `remove`.
  `map`, `filter`, `fold`, `each`, `slice`, `reverse`, and `sort` return new
  values except that `each` is for side effects.
- Import `std.collections.{ HashMap }`: `HashMap.new()`, `from_pairs`, `set`, `get`,
  `get_or`, `contains_key`, `delete`, `size`, `is_empty`, `keys`, `values`,
  `pairs`, and `clear`. Iteration order is unspecified.
- String APIs are `split`, `trim`, `starts_with`, `ends_with`, `find`,
  `replace`, `chars`, `to_upper`, `to_lower`, and `string[].join`.
- String positions and `len(string)` are UTF-8 byte offsets. Strings have no
  direct indexing or public substring operation; use `chars`, `split`,
  `find`, or `replace`.
- `print` and `println` take one value. Use interpolation for several values.
- A non-nullable, non-callable value has `v.debug() -> string`, its structural rendering (`Debug`
  protocol; a string debugs quoted: `"a".debug()` is `"\"a\""`). Primitives
  also have `v.display()` (a string displays unquoted). `"{v}"` and
  `print`/`println` render through a type's own `display` method when it
  declares one, else through `debug`; a nullable renders `null` when absent
  and otherwise exactly like its value. `string.from(v)` renders the same
  text as `"{v}"`. `"{v.debug()}"` forces the debug form. Every nested element,
  field or payload uses its type's `debug` when declared, otherwise builtin
  structure. Nested strings are quoted and escaped, including array and tuple
  elements; multiline custom text is indented at each embedding level.
  `HashMap` declares `display`: JSON-style `"key": value` lines.

## Reflection and definite assignment

- `typeof(value)` is the static type name in value position, a type in type
  position, and a static receiver in `typeof(value).from(other)`.
- `fields(record)` is valid only as a `for` iterable. The compiler unrolls the
  loop over declared fields; `record[field]` projects the current field.
- `let value: T` may omit an initializer, but every path must assign the whole
  value or all default-constructible record fields before reading it.
- A reflective `fun T.decode(self) -> infer!` specializes to the expected type
  at each call site. The target must be known there; external data selects
  values, not types.

## Modules and packages

- One file is one module; `geometry/vec.cz` is `geometry.vec`.
- Two imports cannot bind one local name to different targets, even from the
  same module. Repeating the identical target is allowed.
- Import names with `import path.{ A, B }` or `import path.Name`. Import a
  module with `import path` and use its last segment as qualifier; rename it
  with `import path as local`.
- Names and modules beginning with `_` are private.
- `core` is embedded and its public names form the implicit prelude.
- `std` is an installed package, imported as `std.fs`, `std.net`, etc. It is
  not embedded. A complete packaged toolchain binds it automatically.
- Other imports are relative to the importing module. Declared package names
  take precedence; project files precede `BRASS_INCLUDE` roots.
- `czpm new/init/run/check/fmt/lsp` manages projects and dependencies.
  `czpm check` checks every owned `.cz` file.

## Core API overview

No import is needed for core names:

- I/O: `print`, `println`, `input() -> string!`.
- Arrays and strings: the methods listed above; `len(array_or_string)`.
- Math: `abs`, `min`, `max`, `sqrt`, `floor`, `ceil`, `pow`.
- Conversion: `to_bytes`, `to_text`, `T.from`, `T.parse`, `string.from`.
- Errors: `Result`, `Error`, `error`, `context`.
- Testing/defaults: `assert(condition, message?)`, `T.default()`.
- Reflection/concurrency builtins: `fields`, `typeof`, `spawn`, `with`,
  `sync`.

- Do not declare functions named `len`, `sync`, `error`, `typeof`, `fields`,
  `spawn`, or `with`.
- Bindings shadow `len`, `sync`, and ordinary prelude functions; a module's
  declaration of another prelude name shadows it in that module only.
- Calls of `error`, `typeof`, `fields`, `spawn`, and `with` remain language
  constructs (see [Identifiers and keywords](/references/syntax/#identifiers-and-keywords)).

## Standard library overview

Import these with their complete `std.*` paths:

- `std.fs`: `File`, whole-file read/write, copy/move/remove files and trees,
  and recursive directory creation/removal. Paths accept strings or `Path`.
- `std.path`: lexical `Path` parsing/joining/normalization plus filesystem
  queries, canonicalization, directory entries, and `_PATH` handling.
- `std.process`: `Command`, `Child`, `Stdio`, `Output`, and `exit`. Prefer
  `child.output()` when stdout/stderr are piped to avoid a full-pipe deadlock.
- `std.env`: command arguments, variables, path separator, current directory.
- `std.hash`: MD5/SHA digests, HMAC, incremental `Hasher`, hex conversion,
  and constant-time `equal`. Use SHA-256 or stronger for security decisions;
  these fast hashes are not password hashes.
- `std.regex`: `Regex`, `Match`, `Group`, and `escape`. Patterns are
  linear-time and have no lookaround or backreferences. Brass strings are not
  raw: double `\\` and escape an interpolation brace as `\{`.
- `std.semver`: parse, construct, compare, render, and sort semantic versions;
  build metadata does not affect precedence.
- `std.net`: `Tcp`, `TcpListener`, `Udp`, `Datagram`, and TLS client
  `TlsStream`. TCP is a byte stream, so frame messages or read in a loop.
- `std.url`: RFC 3986 `URI` parsing, reference resolution, path segments, and
  query pairs. Supporting imports are `std.url.authority`,
  `std.url.query`, `std.url.percent`, `std.url.validate`,
  `std.url.charset`, and `std.url.text`.
- `std.http`: HTTP/HTTPS `fetch`, clients, requests, responses, and headers.
  It handles chunked, `Content-Length`, and connection-close response bodies;
  other transfer codings are errors.
- `std.data.json`: `JsonValue` parse/stringify/accessors and typed record
  decoding with `into()`; typed-array decoding is not supported.
- `std.data.toml`: `TomlValue` parse/stringify/accessors and scalar/record
  decoding; decode arrays element by element.

Native-backed `std` modules work in installed native and interpreter builds,
but not in the browser playground.

## Concurrency

Concurrency is native-runtime only:

- `spawn(() -> { ... })` starts a task and is legal only inside a function;
  its closure takes no arguments and returns `void` (or remains open). The
  task may not access a module global that any code writes, nor reassign a
  captured variable; mutate a captured object instead.
- `with(shared, (value) -> { ... })` acquires compiler-managed shared state.
- `sync()` waits for spawned work before its results are observed.

Ownership is inferred; there is no user-facing move/freeze/cown syntax. Keep
blocking operations out of a shared acquisition and call `sync()` before
reading results that tasks mutate.

## Execution and tools

- `brass file.cz`: demand-driven check, native compile, and run.
- `brass check file.cz`: check own code completely and reached dependencies; use in CI.
- `brass --eager file.cz`: the same selected check before anything runs, then run;
  native compilation is first-use in both modes.
- `brass --no-jit-cache file.cz`: run without JIT cache reads or writes;
  put the flag before the program filename, as with `--eager`.
- `brass cache info`: show the shared JIT cache location and usage.
- `brass cache clean`: remove all cached native objects and publication temp
  files older than 24 hours; package downloads are unaffected.
- `brass repl`: eager interpreter session. Concurrency is unavailable. Each
  interactive input runs once; a later input can use only bindings whose
  initializers have no side effects (no calls, interpolation, branches, or
  `!`).
- `czfmt --write file.cz`: format source. `czls`: language server.
- Every run checks from source; only native code is cached
  (`$XDG_CACHE_HOME/brass/jit/`, `BRASS_JIT_CACHE=off` disables it).

## Frequent generation mistakes

- Do not write explicit generic parameters such as `<T>`.
- Do not use `pub`, `impl`, `trait`, `loop`, `defer`, `open(...)`, raw strings,
  string indexing, or language features not listed here.
- Use `Type.Variant`, `Type.static_method`, and `value.instance_method`.
- Use value-preserving implicit numeric conversions only; otherwise call
  `T.from(value)!`.
- Narrow `T?` before use and match Results as `Ok { value }` / `Err { error }`.
- A block-bodied function or closure needs `return` to produce a value.
  `(x) -> { x }` is a block returning `void`; write `(x) -> x`, or
  `(x) -> ({ x })` for a record.
- A closure using `error(...)`/`!` returns a `Result`; unwrap it at the call.
- Compile a `Regex` once rather than inside a loop.
- Run `brass check` after every generated edit.

## Complete example

```brass
type Shape =
    | Circle { radius: float64 }
    | Rectangle { width: float64, height: float64 }

fun area(shape: Shape) -> float64 {
    return match shape {
        Circle { radius } => 3.14159 * radius * radius,
        Rectangle { width, height } => width * height,
    }
}

fun main() {
    const shapes = [
        Shape.Circle { radius: 2.0 },
        Shape.Rectangle { width: 3.0, height: 4.0 },
    ]
    const total = shapes.map((shape) -> area(shape)).fold(
        0.0,
        (sum, value) -> sum + value,
    )
    println("total area = {total}")
}
```
````
