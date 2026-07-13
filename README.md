<div align="center">
  <h1>
    <picture>
      <source media="(prefers-color-scheme: dark)" srcset="book/public/logo/dark.svg">
      <img alt="prepoly" src="book/public/logo/light.svg" width="400">
    </picture>
  </h1>
  <p>
    A statically and flexibly type-inferred scripting language <br>
    with just-in-time compilation
  </p>
  <p>
    <a href="https://prepoly.56.ax">Documentation &amp; Playground</a> |
    <a href="https://prepoly.zulipchat.com/#narrow/channel/614491-announcement">Zulip community</a>
  </p>
</div>

prepoly is a statically type-checked, structurally typed scripting language with
flexible type inference. The name contracts *pre-typed* and *polymorphic*:
it runs like an interpreter, but every function is fully type-checked just before
it executes, and most types are inferred rather than written. A program is run by
a **just-in-time compiler** for native speed, or by an **interpreter** for the
REPL and WebAssembly.

Quick start:

```bash
curl -L https://raw.githubusercontent.com/cordx56/prepoly/refs/heads/main/scripts/install.sh | sh
```

## Features

- **Type inference everywhere.** Flexible inference means most code needs
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
  `!` on a nullable unwraps or returns null early (the return type gains
  `?`), and works at the top level and in `main`, where a failure prints the
  error and exits.
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
- **Tooling:** an interactive REPL and an LSP server (`ppls`).

## Learning the language

Read the **[documentation](https://prepoly.56.ax)**: a step-by-step tutorial,
per-feature guides, language references, and a browser playground, built from
[`book/`](book/). Every language feature also has a runnable example in
[`examples/`](examples/), each checked by `cargo test`.

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

## Status

Sequential execution is the tested, supported path. Two sharp edges are worth
knowing:

- **Concurrency is experimental.** Scheduling is unstructured, so code that must
  observe a spawned task's results calls `sync()` first. Treat it as a preview.
- **The JIT and interpreter agree across the language's tested surface,** but a
  few features are native-only: concurrency (`spawn`/`sync`/`with`) and runtime
  type specialization are refused by the interpreter, so they need the JIT.
  File I/O and the other native libraries run on both back ends (`prepoly repl`
  included); only the browser playground, which cannot load plugins, lacks them.

## License

Mozilla Public License 2.0. See [`LICENSE`](LICENSE).
