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
unused functions unchecked for that run. Only `brass check` gives a complete
whole-program verdict.

## Syntax essentials

- Bindings are `const name = value` or mutable `let name = value`.
- Comments are `//`, `#`, and nestable `/* ... */`. A leading shebang is a
  `#` comment. `/** ... */` directly above a `fun` or `type` is a doc comment.
- Newlines separate statements. A line continues after a binary operator or
  before a leading `.` in a method chain.
- Strings use escapes and `{expression}` interpolation. Escape a literal
  opening brace as `\{`.
- Equality is `==`; `=` is assignment. Compound assignments include `+=`,
  `-=`, `*=`, `/=`, and `%=`.
- `if` and `match` are expressions. Loops are `while condition` and
  `for item in iterable`; `break` and `continue` are supported.
- Closures are `(x) -> expression` or `(x) -> { ...; return value }`.
- Functions and types may be used before their definitions. Top-level
  bindings initialize in textual order and may not be read early.
- Top-level statements run in module dependency order; `main()` runs last if
  present.

```brass norun
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
- Integer literals default to `int32`, or `int64` when needed. Float literals
  default to `float64`. `len` returns `int64`.
- `T[]` is a growable array, `T[n]` a fixed-length array, `[T, U]` a tuple,
  and `[lo..hi]` a half-open integer range.
- `T?` is nullable. Narrow it with `if value`, `if !value { return ... }`, or
  `if let` before using it as `T`.
- `T!` is a fallible Result. See Error handling below.
- Most annotations are optional. An annotation constrains inference; it does
  not opt into type safety.
- Numeric conversions are implicit only when value-preserving. Use
  `T.from(value)!` for checked narrowing or sign changes, `T.parse(text)!` for
  parsing, and `string.from(value)` for text.
- Arrays and records are reference values. Assignment can share them.

## Functions, parameters, and closures

```brass norun
fun distance(x: float64, y: float64) -> float64 {
    return sqrt(x * x + y * y)
}
```

- Return types are inferred when omitted. `void` means no value.
- An unannotated parameter that is only read is passed by shared reference.
  If its body mutates the parameter, the callee receives a private deep copy.
- Use `ref(T)` for an explicit immutable reference and `ref(mut(T))` when the
  callee must mutate the caller's value. `mut(T)` is an explicit mutable copy.
- `infer` is a read-only copied value whose type is inferred; `infer[]`
  requires an array with an inferred element type.
- `self` is a reference, so instance methods can mutate their receiver.
- Closures capture live bindings by reference and may mutate them.
- Closures cannot currently contain `error(...)` or apply `!` to a Result.
  Put fallible work in a named function and call it from the closure.
- Mutual-recursion cycles should annotate their return types.

## Records, methods, sums, and interfaces

Record fields live inside `type`; method implementations live outside it.
An instance method has `self` first. A method without `self` is static.

```brass norun
type Account = {
    owner: string
    balance: int64
}

fun Account.new(owner: string) -> Account {
    return Self { owner: owner, balance: 0 }
}

fun Account.deposit(self, amount: int64) {
    self.balance += amount
}
```

- Construct a record as `Type { field: value, ... }` and call methods as
  `value.method()` or `Type.static_method()`. There is no UFCS.
- A member written as `name(params) -> Return` inside a type is a required
  method signature, not stored data.
- Sum types use `type Name = | Variant { fields } | Empty`. Construct a value
  as `Name.Variant { ... }` and match it as `Variant { ... }`.
- A match on a sum must cover every variant or use `_`.
- `type Child: Parent` declares structural conformance. Members are checked;
  implementations are not inherited. Multiple parents are allowed.
- An unannotated function parameter is structural without an explicit
  interface: only the fields and methods used by the body are required.
- `{ field: value }` is an anonymous record. It can dispatch to exactly one
  in-scope nominal record whose fields and requested method fit.
- `T.from(value) -> T?` performs structural conversion to record type `T`.
- A refined alias such as `type Counts = HashMap { key: string, value: int64 }`
  pins inferred type slots without creating a new nominal type.

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

## Error handling

- `Result` has `Ok { value }` and `Err { error }` variants. Standard failures
  carry an `Error` record with `value`, `location`, `frames`, and `display()`.
- `error(payload)` creates an `Err`. Returning a plain value from a fallible
  function wraps it as `Ok`.
- `result!` unwraps `Ok` or returns the `Err` from the enclosing named
  function. `nullable!` unwraps a value or returns `null` early.
- `result.context(message)` adds trace context only on failure.
- At top level or in `main`, an unhandled `!` prints the error and exits
  non-zero.
- When matching a standard error, print `error.display()` or inspect
  `error.value`; interpolating `{error}` prints the record representation.

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
- `HashMap` is in the prelude: `HashMap.new()`, `from_pairs`, `set`, `get`,
  `get_or`, `contains_key`, `delete`, `size`, `is_empty`, `keys`, `values`,
  `pairs`, and `clear`. Iteration order is unspecified.
- String APIs are `split`, `trim`, `starts_with`, `ends_with`, `find`,
  `replace`, `chars`, `to_upper`, `to_lower`, and `string[].join`.
- String positions and `len(string)` are UTF-8 byte offsets. Strings have no
  direct indexing or public substring operation; use `chars`, `split`,
  `find`, or `replace`.
- `print` and `println` take one value. Use interpolation for several values.

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
- Collections: `HashMap`.
- Reflection/concurrency builtins: `fields`, `typeof`, `spawn`, `with`,
  `sync`.

The compiler-owned names `len`, `spawn`, `with`, `sync`, `error`, `fields`,
and `typeof` cannot be redefined.

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
  It handles `Content-Length` or connection-close bodies, not chunked coding.
- `std.data.json`: `JsonValue` parse/stringify/accessors and typed record
  decoding with `into()`; typed-array decoding is not supported.
- `std.data.toml`: `TomlValue` parse/stringify/accessors and scalar/record
  decoding; decode arrays element by element.

Native-backed `std` modules work in installed native and interpreter builds,
but not in the browser playground.

## Concurrency

Concurrency is native-runtime only:

- `spawn(() -> { ... })` starts a task and is legal only inside a function.
- `with(shared, (value) -> { ... })` acquires compiler-managed shared state.
- `sync()` waits for spawned work before its results are observed.

Ownership is inferred; there is no user-facing move/freeze/cown syntax. Keep
blocking operations out of a shared acquisition and call `sync()` before
reading results that tasks mutate.

## Execution, caching, and tools

- `brass file.cz`: demand-driven check, native compile, and run.
- `brass check file.cz`: complete check without execution; use in CI.
- `brass --eager file.cz`: complete check before anything runs, then run;
  native compilation is first-use in both modes.
- `brass repl`: eager interpreter session. Concurrency is unavailable.
- `czfmt --write file.cz`: format source. `czls`: language server.
- `.czcache` may be a full check or a partial normal-run snapshot; file
  existence alone is not a complete verdict. `BRASS_CACHE=off` disables
  analysis caches.

## Frequent generation mistakes

- Do not write explicit generic parameters such as `<T>`.
- Do not use `pub`, `impl`, `trait`, `loop`, `defer`, `open(...)`, raw strings,
  string indexing, or language features not listed here.
- Use `Type.Variant`, `Type.static_method`, and `value.instance_method`.
- Use value-preserving implicit numeric conversions only; otherwise call
  `T.from(value)!`.
- Narrow `T?` before use and match Results as `Ok { value }` / `Err { error }`.
- A block-bodied function or closure needs `return` to produce a value.
- Do not put fallible propagation directly in a closure.
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
