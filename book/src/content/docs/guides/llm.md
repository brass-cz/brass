---
title: "LLM agents"
description: "A system prompt that teaches LLM agents to write valid Brass."
---

Brass is new enough that an LLM has not seen it during training, so an agent
will otherwise write code in the dialect of whatever language the syntax most
resembles. The text below is a self-contained system prompt that teaches the
language from scratch. Drop it into your agent's project instructions (for
example `AGENTS.md` or `CLAUDE.md`) so the agent writes valid Brass.

````markdown
# Writing Brass

You are writing **Brass**, a statically type-checked, structurally typed
scripting language with flexible (Hindley-Milner-style, but not textbook HM)
type inference. It runs like a script, with no build step, but every function
is fully type-checked just before it runs. Source files use the `.cz`
extension. Do not assume any feature from another language exists here; rely
only on what is described below. After writing code, type-check it with
`brass check file.cz`: a plain `brass file.cz` run checks LAZILY (only the
code the run actually executes), so a successful run does not prove the
whole file well-typed; `brass check` does.

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

- Comments: `// line`, `# line` (so a leading `#!/usr/bin/env brass`
  shebang is valid), and `/* block, which may nest */`. A `/** doc comment */`
  written directly above a `fun` or `type` declaration documents it (shown by
  editor tooling); use one per public declaration.
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
that structurally has the members it uses. No interface or inheritance is
needed:

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
  `!` operator propagates: `expr!` unwraps `Ok` or returns the `Err` early
  from the enclosing function.
- On a NULLABLE operand, `expr!` unwraps the value and a null returns null
  itself early: the enclosing function's return type gains an outer `?`
  (`fun pick() { return find()! }` is `-> T?`, not fallible). Mixing bare
  returns, `error(...)`, and a nullable `!` in one body infers
  `Result<T, E>?`: narrow the `?` with `if r { ... }`, then match.
- `!` also works at the module top level and in `main`: a failed
  propagation there (an `Err` or a null) prints `unhandled error: ...` and
  exits non-zero instead of returning.
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
means declared in or imported into the current module; an anonymous value
never adopts a type the module has not imported (a value already carrying a
nominal type, e.g. an imported function's return, dispatches methods without
importing the type name). Several satisfying types make the call ambiguous (a
compile error at the value asking for an annotation); a missing field is
reported at the value with the unsatisfied constraint. For a record type `T`,
`T.from(v)` yields `T?`: the record value when `v` structurally has all of
`T`'s fields (decided at that call site), else `null`. `v` may be of ANY
type, since one that is not a record at all has none of `T`'s fields, so the
conversion answers `null` rather than failing to compile; this is how one
function takes a value whose type differs per call site (`Path.from(x)` reads
as "when this is a Path"). Pair it with `if let`:

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
`ret` fully initialized. `typeof(x)` names `x`'s static type: a string in
value position (`print(typeof(x))`), a type in type position (`let y:
typeof(x)`), and a static receiver (`typeof(x).from(v)`). Both read only the
type, so they are allowed on an uninitialized binding.

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
(`geometry/vec.cz` is the module `geometry.vec`). Import selected names with
`import path.{ A, B }`, one name with `import path.Name`, or the whole module
with `import path`: its exports are then used qualified by the path's last
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

## Core library (implicit prelude, no import needed)

Everything in this section is in scope with no import.

- IO: `print(value)` and `println(value)` take exactly ONE argument; combine
  several values with interpolation (`println("{a} {b}")`).
  `input() -> string!` reads one stdin line without its trailing newline.
- `len(x) -> int64`: the element count of an array, or the BYTE length of a
  string. Also callable as a method: `arr.len()`, `s.len()`.
- `assert(cond)` / `assert(cond, msg)` aborts the program when `cond` is false.
- Numeric limits: `INT32_MAX`, `INT32_MIN`, `INT64_MAX`, `INT64_MIN`.
- Identifiers beginning with `_` (e.g. `_string_bytes`, `_panic`, `_argv`) are
  runtime internals: do not call them directly; use the wrappers below.

### Array methods

Mutating, on dynamic `T[]` arrays only: `arr.push(x)`, `arr.pop() -> T?`,
`arr.insert(i, x)`, `arr.remove(i) -> T`.

Everything else returns a NEW array; nothing sorts, maps, or reverses in
place:

- `arr.map(f)`, `arr.filter(pred)`, `arr.fold(init, f)` (left fold),
  `arr.each(f)` (side effects only, returns nothing)
- `arr.slice(start, end)`: a copy, `end` exclusive; the bounds are `int64`,
  so `arr.slice(1, arr.len())` works
- `arr.reverse()`; `arr.sort()`: ascending by `<`
- `arr.contains(x) -> bool`: whole-element `==` (a substring test on a
  string is `s.find(sub) != null`, not `contains`)
- `parts.join(sep) -> string`: on a `string[]`

### String methods (all offsets are UTF-8 BYTE offsets)

- `s.split(sep) -> string[]`: keeps interior and trailing empty fields
  (`"a,,b,"` -> `["a", "", "b", ""]`); an empty `sep` yields `[s]` unsplit
- `s.trim() -> string`: ASCII whitespace off both ends
- `s.starts_with(prefix) -> bool`, `s.ends_with(suffix) -> bool`
- `s.find(sub) -> int64?`: byte offset of the first occurrence, null if
  absent
- `s.replace(old, new) -> string`: every occurrence; an empty `old` is a
  no-op
- `s.chars() -> string[]`: one string per character, multibyte kept whole
- `s.to_upper()` / `s.to_lower()`: ASCII letters only
- There is no substring slicing and no `s[i]` indexing: work through
  `chars()`, `split`, `find`, `replace`.

### Math

- `abs(x)`, `min(a, b)`, `max(a, b)`: polymorphic over any ordered type
- `sqrt(x)`, `floor(x)`, `ceil(x)`, `pow(base, exp)`: return `float64`; the
  arguments are floats (an int argument widens only when value-preserving, so
  convert an `int64` with `float64.from(n)` first)

### Conversions

- `string.from(x) -> string`: any value's text, as `print` renders it
- `float64.from(x) -> float64`: infallible widening
- `int32.from(x) -> int32!` etc.: checked for every numeric type; fails
  when the value does not fit
- `int32.parse(s) -> int32!`, `float64.parse(s) -> float64!` etc.: parse
  decimal text
- `to_bytes(s) -> uint8[]` / `to_text(bytes) -> string!`: string/byte
  conversions (pair them with fs and net)
- Free-function aliases: `int32_from`, `int32_parse`, `float64_from`,
  `float64_parse`, `string_from`.

## HashMap (in the prelude, no import needed)

An open-addressing hash map, in the core module `core.collections` -- part
of the implicit prelude, so NO import is needed. Keys may be of any type that renders to a stable string and
compares with `==` (integers, strings, records); values may be of any type.
`HashMap.new()` takes NO arguments; the key/value types are inferred from
the first `set` (`let m = HashMap.new(); m.set("a", 1)` is a
`string -> int32` map). To pin them explicitly, use a refinement alias:
`type Counts = HashMap { key: string, value: int64 }`.

- `HashMap.new()`; `HashMap.from_pairs([[k, v], ...])`
- `m.set(k, v)`: insert or overwrite
- `m.get(k) -> V?`: null when absent; `m.get_or(k, default) -> V`: never
  nullable
- `m.contains_key(k) -> bool`; `m.delete(k) -> bool` (whether it was present)
- `m.size() -> int64`; `m.is_empty() -> bool`
- `m.keys() -> K[]`, `m.values() -> V[]`, `m.pairs() -> [K, V][]`: all in
  unspecified (slot) order
- `m.clear()`: keeps capacity and key/value types

## Standard library (`import std.*`)

The toolchain ships a `std/` directory imported with the `std.` prefix. A
distributed install binds it automatically beside its binary; from a repo
checkout, build the native plugin halves once with `std/build.sh` and set
`BRASS_PACKAGES=std=<repo>` (the path is the directory CONTAINING `std/`).
Every module below runs on BOTH back ends (the JIT and `brass repl`); only
`spawn` concurrency is JIT-only.

### env: `import std.env.{ args, var, vars, path_separator, current_dir }`

- `args() -> string[]`: the program's argument vector, the program file as
  written on the command line, then everything after it, verbatim
  (`brass main.cz --verbose x` -> `["main.cz", "--verbose", "x"]`; the
  driver consumes nothing after the file). Empty in an interactive REPL.
- `var(name) -> string!`: the variable's value; UNSET is an error, not `""`
- `vars()`: every environment variable, as a `string -> string` HashMap
- `path_separator() -> string`: the OS separator for path-list environment
  variables (`:` on Unix, `;` on Windows)
- `current_dir() -> Path!`: the working directory, as a `path` `Path`

### path: `import std.path.{ Path }`

A `Path` is a list of components. Everything except the filesystem queries at
the end is pure: it never touches the OS and works for paths that do not
exist. Every module also has a private constant `_PATH: string` holding its
own absolute source path, so "the file I am in" is `Path.parse(_PATH)`.

- Construct: `Path.parse(s)`; `Path.current_dir() -> Path!`;
  `Path.home() -> Path!`; `Path.temp_dir() -> Path!`
- Render: `p.to_string()` (the empty path prints as `.`);
  `p.components() -> string[]`; `p.depth() -> int64` (component count, NOT
  `len`, which paths do not support)
- Predicates: `p.is_absolute()`, `p.is_root()`, `p.equals(q)`,
  `p.starts_with(base: Path)` (component-wise prefix)
- Take apart: `p.parent() -> Path`; `p.basename() -> Path`;
  `p.extension() -> string?` (text after the LAST dot; `.gitignore` has
  none); `p.stem() -> string`; `p.with_extension(ext) -> Path` (`ext`
  without the dot; `""` removes it)
- Combine: `p.join(x) -> Path`: `x` may be a string (`"src/main.cz"`), a
  `string[]`, or another `Path`; an ABSOLUTE `x` replaces `p` entirely
- Resolve: `p.normalize()` (fold `.`/`..` textually);
  `p.to_absolute() -> Path!` (against the cwd; no symlink resolution);
  `p.to_relative(base: Path) -> Path!`; `p.canonicalize() -> Path!`
  (symlinks resolved; the path must exist)
- Filesystem queries: `p.exists()`, `p.is_dir()`, `p.is_file()`,
  `p.is_sym_link() -> bool`; `p.read_link() -> Path!`;
  `p.entries() -> Path[]!` (directory listing, OS order);
  `p.file_size() -> int64!`

### fs: `import std.fs.{ File, read_file, write_file, create_dir, remove_dir }`

- `read_file(path) -> string!`; `write_file(path, content) -> void!`
- `copy_file(source, target) -> void!` / `move_file(source, target) -> void!`:
  both REPLACE an existing target; `move_file` is a rename, falling back to
  copy+delete across filesystems. `remove_file(path) -> void!`. A DIRECTORY is
  refused by move_file/remove_file, and a MISSING file is an ERROR.
- `copy_dir(source, target) -> void!` / `move_dir(source, target) -> void!`:
  the whole tree; unlike the file forms these REFUSE an existing target (call
  `remove_dir` first), and refuse a target inside the source. A symlink in the
  tree is recreated as a link, not followed.
- `copy(source, target)` / `move(source, target)`: take EITHER kind,
  dispatching on what `source` is; each half keeps its own target rule.
- `create_dir(path) -> void!`: RECURSIVE (`mkdir -p`); an existing directory
  is success. `remove_dir(path) -> void!`: RECURSIVE (`rm -r`); a missing
  directory is an ERROR.
- EVERY path here may be a string OR a `path` `Path` (`File.open`, `read_file`,
  `write_file`, `create_dir`, `remove_dir`); no `to_string()` needed.
- `File.open(path, mode) -> File!`: mode `"r"` read, `"w"` truncate+create,
  `"a"` append+create
- `f.read(max) -> uint8[]!`: up to `max` bytes, fewer on a short read,
  empty at end-of-file; `f.write(data: uint8[]) -> int64!`;
  `f.seek(pos) -> void!` (absolute); `f.close() -> void!` (idempotent;
  standard streams are never closed)
- `f.size() -> int64!`: answered by path, so ONLY for files opened by
  `open`; adopted descriptors and standard streams report an error
- `File.from_fd(fd)` adopts an open descriptor (a pipe, a socket);
  `File.stdin()`, `File.stdout()`, `File.stderr()`
- Text <-> bytes with the prelude `to_bytes` / `to_text`

### process: `import std.process.{ Command, Stdio }`

`Stdio = Inherit | Pipe | Null` (default `Inherit`). The builder methods
mutate the command and return it, so they chain:

```
const child = Command.new("git").args(["status"]).stdout(Stdio.Pipe).spawn()!
const out = child.output()!    // { code: int32, stdout: uint8[], stderr: uint8[] }
println(to_text(out.stdout)!)
```

- `Command.new(program)` (looked up on `PATH`), then `.arg(v)`, `.args(vs)`,
  `.env(name, value)`, `.stdin(m)`, `.stdout(m)`, `.stderr(m)`, then
  `.spawn() -> Child!`
- `.env` ADDS to the inherited environment (or overrides one entry); the child
  always inherits this process's variables, and there is no way to unset one
- `exit(code: int64)`: ends THIS process (not a child) with that code and
  never returns; stdout/stderr are flushed first, so a pending `print` is not
  lost. Only the low 8 bits reach the caller (`exit(256)` reports 0).
- `child.output() -> Output!`: drains the piped streams while waiting, then
  returns `{ code, stdout, stderr }`; cannot deadlock. Prefer this.
- `child.wait() -> int32!`: the exit code; DEADLOCKS if a `Pipe` stream
  fills unread (~64KiB), so drain pipes first or use `output()`
- `child.stdin()/stdout()/stderr() -> File!`: the pipe as an fs `File`
  (requires that stream be `Stdio.Pipe`); write to stdin, read the others

### hash: `import std.hash.{ sha256, hmac_sha256, hex, equal, Hasher }`

Message digests and HMAC. A digest is a `uint8[]` (raw bytes); hash text by
its UTF-8 bytes and render with `hex`:
`println(hex(sha256(to_bytes("abc"))))`.

- `md5`, `sha1`, `sha224`, `sha256`, `sha384`, `sha512`: all
  `(uint8[]) -> uint8[]`, INFALLIBLE (16/20/28/32/48/64 bytes)
- `hmac_sha1`, `hmac_sha256`, `hmac_sha512`: `(key: uint8[], data: uint8[])
-> uint8[]`; any key length works
- `hex(bytes) -> string` (lowercase); `unhex(text) -> uint8[]!` (the inverse;
  accepts upper case, fails on an odd length or a non-hex character)
- `equal(a, b) -> bool`: CONSTANT-TIME digest/MAC comparison
- `Hasher`: the incremental form when the input is not in memory at once:
  `let h = Hasher.sha256()!` (also `.md5()/.sha1()/.sha224()/.sha384()/
.sha512()`), then `h.update(bytes)!` repeatedly, then `h.finalize()!`.
  `finalize` CONSUMES the hasher: a second call is an error.

SECURITY: `md5`/`sha1` are broken against collisions, so they are for interop
only, never a security decision; prefer `sha256`. Authenticate with
`hmac_sha256`, NOT `sha256(key + data)` (length-extension forgeable). Compare
a MAC with `equal`, not `==`. These are FAST hashes: password storage needs a
slow KDF (argon2/scrypt/bcrypt), which this library deliberately does not
provide.

### regex: `import std.regex.{ Regex, escape }`

Rust's `regex` engine: linear-time matching, so NO backreferences (`\1`) and
NO lookaround (`(?=..)`, `(?<=..)`); a pattern using one fails to compile.
Everything else is standard (classes, `{m,n}`, alternation, `^`/`$`/`\b`,
`(?:..)`, `(?<name>..)`, inline flags `(?i)(?m)(?s)(?x)`).

WRITING A PATTERN: a Brass string is NOT raw and it interpolates `{expr}`:

- double every backslash: `\\d`, `\\w`, `\\b`
- escape an opening brace: `"\\d\{4}"`. Writing `"\\d{4}"` SILENTLY compiles
  as `\d4` (the `{4}` interpolates to the text `4`), which still matches
  things; this is the #1 mistake. A closing brace needs no escape.
- in a replacement, prefer `$1` / `$name` over `${name}` (same brace problem)

```
const date = Regex.new("(?<year>\\d\{4})-(\\d\{2})-(\\d\{2})")!   // fallible
if let m = date.find("due 2026-07-13") {          // Match?, null when no match
    println("{m.text} {m.start} {m.end}")         // 2026-07-13 4 14 (BYTE offsets)
    if let y = m.named("year") { println(y.text) }
}
println(date.replace_all("2026-07-13", "$year/$2"))
```

- `Regex.new(pattern) -> Regex!`: the ONLY fallible call; every method below
  is infallible. Compile ONCE (a Regex is never released; compiling in a loop
  grows the process).
- `re.is_match(text) -> bool`; `re.find(text) -> Match?`;
  `re.find_from(text, from: int64) -> Match?`; `re.find_all(text) -> Match[]`
- `re.replace(text, rep) -> string` (first) / `re.replace_all(text, rep)`
- `re.split(text) -> string[]`; `re.group_count() -> int64` (counts group 0)
- `escape(text) -> string`: a pattern matching `text` literally
- `Match` = `{ text, start, end, groups: Group?[] }` (`groups[0]` is the whole
  match); `m.group(i) -> Group?`, `m.named("year") -> Group?`: both null when
  the group did not participate. `Group` = `{ text, start, end }`.

### semver: `import std.semver.{ Version, sort }`

Semantic Versioning 2.0.0, parsed with the official semver.org pattern (so
`v1.0.0`, `1.0`, and `01.0.0` are all REJECTED).

- `Version.parse(text) -> Version!`; `Version.new(major, minor, patch) -> Version`
- `Version` = `{ major, minor, patch: int64, prerelease: string?, build: string? }`;
  the optional parts are `null` when absent
- `v.to_string() -> string`; `v.is_prerelease() -> bool`;
  `v.prerelease_ids() -> string[]` (`"rc.1"` -> `["rc", "1"]`)
- `v.compare(other) -> int64` (-1/0/1); `v.equals/less_than/greater_than(other)
-> bool`; `sort(versions: Version[]) -> Version[]` (a new array, ascending)

PRECEDENCE: a pre-release PRECEDES its release (`1.0.0-rc.1 < 1.0.0`); numeric
pre-release identifiers compare numerically (`beta.2 < beta.11`) and precede
alphanumeric ones; BUILD METADATA IS IGNORED (`1.0.0+a` equals `1.0.0+b`).

### net: `import std.net.{ Tcp, TcpListener, Udp, TlsStream }`

TCP is a BYTE STREAM: one `read` may return part of a message, so loop or
frame messages. Bytes convert with the prelude `to_bytes` / `to_text`.

- `Tcp.connect(host, port) -> Tcp!`: `host` is an IP literal or a name
- `TcpListener.bind(host, port) -> TcpListener!`: port 0 = OS-chosen (read
  it back with `local_addr()`); `listener.accept() -> Tcp!`;
  `listener.local_addr() -> string!`; `listener.close()`
- On a `Tcp`: `read(max) -> uint8[]!` (empty at end-of-stream),
  `write(data) -> int64!`, `close()`, `local_addr() -> string!` /
  `peer_addr() -> string!` (both `"ip:port"`), `set_timeout(ms)` (0 = block
  forever; an exceeded deadline is an error Result)
- `Udp.bind(host, port) -> Udp!`; `sock.send_to(data, host, port) -> int64!`;
  `sock.recv_from(max) -> Datagram!` with `Datagram = { data: uint8[],
addr: string }` (a longer datagram truncates); plus `local_addr`,
  `set_timeout`, `close`
- `TlsStream.connect(host, port) -> TlsStream!`: TLS with certificate
  verification against `host` (bundled Mozilla roots, no configuration
  knobs); then `read`/`write`/`close` exactly like `Tcp`

### url: `import std.url.{ URI }`

An RFC 3986 parser. Components KEEP their percent-encoding (use the decoded
views below); null means the component was ABSENT, which differs from empty
(`http://h/p` has a null query, `http://h/p?` an empty one). `scheme` comes
back lowercased.

- `URI.parse(s) -> URI!` (requires a scheme);
  `URI.parse_reference(s) -> URI!` (relative references allowed)
- Fields: `scheme: string?`, `authority: Authority?`, `path: string`,
  `query: string?`, `fragment: string?`; `Authority` is
  `{ userinfo: string?, host: string, port: uint16? }`
- `uri.to_string()` reassembles; `uri.authority_string() -> string?`
- Decoded views: `uri.path_segments() -> string[]!` and
  `uri.query_pairs() -> QueryPair[]!` (`QueryPair = { key: string,
value: string }`, from `import url.query.{ QueryPair }`)
- Percent-coding: `import url.percent`, then `percent.decode(s) -> string!`
  and `percent.encode_component(s) -> string`

### http: `import std.http.{ fetch, HttpClient, HttpRequest, HttpResponse, Header }`

HTTP/1.1 over `net`. Response bodies are read by `Content-Length` (or to
connection close); chunked transfer coding is NOT decoded.

- `fetch(url) -> HttpResponse!`: GET an `http://` or `https://` URL string
- `HttpClient.http(host, port)` / `HttpClient.https(host, port)`, then
  `client.fetch(path)!` or `client.request(req)!`
- `HttpRequest = { method, path, version, headers: Header[], body: uint8[] }`
  with `Header = { name: string, value: string }`;
  `HttpRequest.parse(raw: string)!` (a STRING, so a serialized `uint8[]`
  round-trips through `to_text(bytes)!` first); `req.serialize() -> uint8[]`
- `HttpResponse = { version, status: int32, reason, headers, body }`;
  `resp.body_text() -> string!`; `HttpResponse.parse(raw: string)!`;
  `resp.serialize() -> uint8[]` (the bytes a server writes; nothing is added,
  so `Content-Length` is yours to set, as with the request)
- `request(req) -> HttpResponse!`: plain HTTP; the host comes from the
  request's `Host` header

### JSON: `import std.data.json.{ JsonValue }`

Pure Brass (no plugin).

```
type JsonValue =
    | Null
    | Bool { value: bool }
    | Number { value: float64 }
    | String { value: string }
    | Array { value: JsonValue[] }
    | Object { values }              // a string -> JsonValue HashMap
```

- `JsonValue.parse(text) -> JsonValue!`: the whole input must be one JSON value
- `v.stringify() -> string`: compact output; object members render in the map's
  slot order, not the source document's order
- Accessors on a `JsonValue`: `get(key) -> JsonValue!` (objects),
  `at(index) -> JsonValue!` (arrays), `as_bool() -> bool!`,
  `as_number() -> float64!`, `as_string() -> string!`, `is_null() -> bool`
- `j.into()!` decodes into the type the CALL SITE expects
  (`const u: User = j.into()!`): scalars, nullables, and records whose
  field names match the JSON keys, recursively. A JSON ARRAY cannot be
  decoded with `into` (even as a record field); walk arrays with `at`.

## Concurrency (experimental, avoid unless asked)

The only primitives are `spawn(f)` (run a closure on a thread), `with(c, f)`
(acquire a shared object to read/use it), and `sync()` (wait for spawned work
before observing its results). The compiler infers ownership automatically; you
never write move/freeze/cown. `spawn` is only legal inside a function (a
top-level `spawn` is a compile error). Spawned work is otherwise joined only
at the end of `main`, so insert `sync()` before a read that may race ahead.

## Common mistakes to avoid

- Implicit numeric conversion is value-preserving widening ONLY. Narrowing
  (smaller width, sign change, `float64 -> float32`, `int64 -> float64`,
  float -> int) always goes through `T.from(x)!`.
- `len()` returns `int64`; implicit int widening covers the common cases
  (`[0..len(xs)]` works without an annotation).
- `print`/`println` take exactly one argument; interpolate instead.
- `map`/`filter`/`sort`/`reverse`/`slice` return NEW arrays; only
  `push`/`pop`/`insert`/`remove` mutate.
- Use `==` for equality, not `=`.
- A nullable (`T?`) value cannot be used until narrowed by an `if` guard.
- Match `Result` with the field names `Ok { value }` / `Err { error }`.
- Construct sum-type values as `Type.Variant { ... }`, and call static methods
  as `Type.method(...)`.
- Block-bodied closures and functions need an explicit `return`; expression
  bodies (`(x) -> x + 1`) do not.
- The `!` error-propagation operator needs a fallible context, the top
  level, or `main`; a function explicitly annotated with a non-Result
  return type rejects `expr!` in its body.
- A fallible function that returns no value may be annotated `-> void!`:
  falling off the end of the body (or a bare `return`) is its Ok exit.

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
