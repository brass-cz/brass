<div align="center">
  <h1>
    prepoly
  </h1>
  <p>
    A statically and flexibly type-inferred programming language
  </p>
  <p>
    with just-in-time compilation
  </p>
  <p>
    <a href="https://prepoly.56.ax">Documentation &amp; Playground</a> |
    <a href="https://prepoly.zulipchat.com/join/ypl6haeltx6a2z24rz2vd5pp/">Zulip community</a>
  </p>
</div>

prepoly is a statically type-checked, structurally typed language with
Hindley-Milner type inference. The name contracts *pre-typed* and *polymorphic*:
it runs like an interpreter, but every function is fully type-checked just before
it executes, and most types are inferred rather than written. A program is run by
a **just-in-time compiler** for native speed, or by an **interpreter** for the
REPL and WebAssembly.

Quick start:

```bash
curl -L https://raw.githubusercontent.com/cordx56/prepoly/refs/heads/main/scripts/installer | sh
```

## Features

- **Type inference everywhere.** Hindley-Milner inference means most code needs
  no annotations; types are resolved per function, just before it runs.
- **Records and sum types** under one `type` keyword. Methods are implemented
  with `fun T.m(...)`: a first `self` parameter makes an instance method,
  otherwise it is static; `Self` refers to the type.
- **Structural subtyping with interface contracts.** `type B: A` requires `B` to
  provide every member of `A`, checked at compile time; plain functions accept
  any value that has the members they use, with no inheritance.
- **Exhaustive pattern matching** with `match` and `if let`.
- **Nullable and Result.** `T?` is narrowed by `if`; `T!` is a `Result`, with
  `error(x)`, `expr!` early-return propagation, and automatic `Ok` wrapping.
- **Structural conversion.** `T.from(v)` for a record type `T` yields `T?` — the
  record when `v` structurally has all of `T`'s fields, else null — so
  `if let p = T.from(v)` branches on the actual value.
- **References with inferred mutability.** An unannotated parameter is passed by
  reference and its mutability is inferred; `infer` deep-copies instead; `ref(T)`
  and `ref(mut(T))` are explicit. Closures capture by mutable reference.
- **Tuples** `[T, U]`, anonymous structural records, string interpolation, and
  both explicit and automatic numeric conversion.
- **A file-based module system** where each file is a module and a leading `_`
  marks a private name, plus a small standard library written in prepoly itself.
- **Experimental concurrency.** `spawn(f)`, `with(cown, f)`, and `sync()` are the
  primitives; the compiler infers ownership, never the programmer.
- **Tooling:** an interactive REPL and an LSP server (`prepoly-lsp`).

## Language tour

### Types and pattern matching

`type` defines both records and sum types. A member is a field, or a method
*signature* (an interface requirement). Methods are implemented outside the type
with `fun T.m(...)` — an instance method when its first parameter is `self`,
otherwise static. `match` over a sum type is checked for exhaustiveness.

```
type Shape =
    | Circle { radius: float64 }
    | Rectangle { width: float64, height: float64 }
    | Point

fun area(s: Shape) -> float64 {
    return match s {
        Circle { radius } => 3.14159 * radius * radius,
        Rectangle { width, height } => width * height,
        Point => 0.0,
    }
}
```

### Interfaces

`type B: A` makes `B` satisfy `A` structurally; a function with no annotation
accepts anything that has the members it uses.

```
type Showable = { to_string(self) -> string }

type User: Showable = {
    name: string
}

fun User.to_string(self) -> string { return self.name }

fun print_info(obj) { println(obj.to_string()) }   // accepts anything Showable
```

### Nullable and Result

```
fun parse_positive(s: string) {
    let n = int32.parse(s)!            // returns early on failure
    if n < 0 { return error("negative") }
    return n                           // wrapped in Result.Ok
}

let x: int32? = first_even(nums)
if x { println("got {x}") }            // x is int32 inside the guard
```

### References and mutability

An argument without a type annotation is a reference whose mutability is
inferred, so a function can mutate its caller's value. `infer` opts out and
deep-copies instead.

```
fun double(a) {                  // a is a mutable reference
    for e in a { e *= 2 }
}
let arr = [1, 2, 3]
double(arr)
println(arr)                     // [2, 4, 6]

fun untouched(a: infer) {        // a is deep-copied
    for e in a { e *= 2 }
}
const xs = [1, 2, 3]
untouched(xs)
println(xs)                      // [1, 2, 3]
```

### Modules

One file is one module and the directory layout is the module path. Public names
(no leading `_`) can be imported; an import path is resolved relative to the
importing file.

```
import students.types.{ Student }    // students/types.pp
```

### Concurrency

```
spawn(() -> { for n in nums { counter.add(n) } })
sync()                               // wait for spawned work before observing it
with(counter, (c) -> { println("total = {c.total}") })
```

## Building

The native build links **LLVM** statically for the JIT. Rather than require a
system LLVM, the `./x` wrapper downloads a prebuilt LLVM into `./llvm/` on first
use and runs cargo with it on the path. Use `./x` in place of `cargo`:

```sh
./x cargo build --release        # downloads LLVM on first run -> ./target/release/prepoly
./x cargo test --workspace
./x cargo clippy --workspace --all-targets
```

LLVM is needed only by the JIT. An interpreter-only build needs no LLVM and uses
plain `cargo`:

```sh
cargo build -p prepoly_driver --no-default-features # interpreter only, no LLVM
```

prepoly also builds for `wasm32-wasip1`, where it runs through the interpreter.

## Running programs

```sh
prepoly       path/to/file.pp     # type-check and run (the LLVM JIT when available)
prepoly check path/to/file.pp     # type-check only
prepoly repl  path/to/file.pp     # run a file through the interpreter
prepoly repl                      # interactive interpreter session
prepoly                           # no arguments: same interactive session
```

A bare file argument is type-checked and then run on the JIT when it is built in,
otherwise on the interpreter. Each module's top-level statements run in dependency
order, then `main` is called if defined. The standard library is an implicit
prelude.

A tutorial lives in [`book/`](book/) (mdBook), and every language feature has a
runnable example in [`examples/`](examples/), each checked by `cargo test`.

## Status

Sequential execution is the tested, supported path. Two sharp edges are worth
knowing:

- **Concurrency is experimental.** Scheduling is unstructured, so code that must
  observe a spawned task's results calls `sync()` first. Treat it as a preview.
- **The JIT and interpreter agree across the language's tested surface,** but a
  few runtime-only features differ: file I/O and concurrency currently require
  the native runtime rather than `prepoly repl`.

## License

Mozilla Public License 2.0. See [`LICENSE`](LICENSE).
