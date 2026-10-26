<div align="center">
  <h1>
    <picture>
      <source media="(prefers-color-scheme: dark)" srcset="book/public/logo/dark.svg">
      <img alt="Brass" src="book/public/logo/light.svg" width="400">
    </picture>
  </h1>
  <p>
    A statically and flexibly type-inferred scripting language <br>
    with just-in-time compilation
  </p>
  <p>
    <a href="https://brass-cz.org">Documentation</a> |
    <a href="https://brass-cz.org/playground/">Playground</a> |
    <a href="https://github.com/brass-cz/codespace">Codespaces</a> |
    <a href="https://brass.zulipchat.com/#narrow/channel/618307-announcement">Zulip community</a>
  </p>
</div>

Brass is a statically typed, structurally typed scripting language with
flexible type inference. Its `.cz` source extension comes from *copper* and
*zinc*, the two metals that make up brass. A Brass program runs like a script,
but every function is fully type-checked just before it executes, and most
types are inferred rather than written. A **just-in-time compiler** runs the
program at native speed; an **interpreter** backs the REPL and WebAssembly.

Quick start:

```bash
curl -fsSL https://raw.githubusercontent.com/brass-cz/brass/refs/heads/main/scripts/install.sh | sh
```

Then,

```bash
export PATH="$HOME/.brass/bin:$PATH"
# Create new package
czpm new hello-world
cd hello-world
# Run
czpm run
```

## Features

- **Type inference everywhere.** Flexible inference means most code needs
  no annotations; an unannotated function is checked at each call's argument
  types, just before it runs.
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
- **Structural conversion.** `T.from(v)` for a record type `T` yields `T?`: the
  record when `v` structurally has all of `T`'s fields, null otherwise. So
  `if let p = T.from(v)` branches on the actual value.
- **Inferred parameter passing.** An unannotated parameter is a shared
  reference when the body only reads it and a private deep copy when the body
  mutates it. `ref(T)` (read-only reference), `ref(mut(T))` (writes through to
  the caller), `mut(T)` (mutable copy), and `infer` (read-only copy) are
  explicit. Closures capture by mutable reference.
- **Tuples** `[T, U]`, anonymous structural records, string interpolation, and
  both explicit and automatic numeric conversion.
- **A file-based module system** where each file is a module and a leading `_`
  marks a private name, plus a small standard library written in Brass itself.
- **Experimental concurrency.** `spawn(f)`, `with(cown, f)`, and `sync()` are the
  primitives; the compiler infers ownership, never the programmer.
- **Tooling:** an interactive REPL and an LSP server (`czls`).

## Learning the language

Read the **[documentation](https://brass-cz.org)**: a step-by-step tutorial,
per-feature guides, language references, and a browser playground, built from
[`book/`](book/). Every language feature also has a runnable example in
[`examples/`](examples/), each checked by `cargo test`.

## Building

The native build links **LLVM** statically for the JIT. Rather than require a
system LLVM, the `./x` wrapper downloads a prebuilt LLVM into `./llvm/` on first
use and runs cargo with it on the path. Use `./x` in place of `cargo`:

```sh
./x cargo build --release        # downloads LLVM on first run -> ./target/release/brass
./x cargo test --workspace
./x cargo clippy --workspace --all-targets
```

LLVM is needed only by the JIT. An interpreter-only build needs no LLVM and uses
plain `cargo`:

```sh
cargo build -p brass_driver --no-default-features # interpreter only, no LLVM
```

Brass also builds for `wasm32-wasip1`, where it runs through the interpreter.

## Running programs

```sh
brass       path/to/file.cz     # type-check and run (the LLVM JIT when available)
brass check path/to/file.cz     # type-check only
brass repl  path/to/file.cz     # run a file through the interpreter
brass repl                      # interactive interpreter session
brass                           # no arguments: same interactive session
```

A bare file argument runs on the JIT when it is built in, otherwise on the
interpreter. The JIT run checks each function before it executes but does not
wait for code the run never needs; `--eager` checks the whole program first, as
`brass check` does. Each module's top-level statements run in dependency order,
then `main` is called if defined. The embedded `core` library is an implicit
prelude; the shipped `std` library is imported as `std.*`. Everything after the
program file is passed through verbatim and is available from `env.args()`;
driver flags such as `--eager` must come before the file:

```sh
brass --eager path/to/file.cz input.txt --verbose
```

## Status

Sequential execution is the tested, supported path. Two sharp edges are worth
knowing:

- **Concurrency is experimental.** Scheduling is unstructured, so code that must
  observe a spawned task's results calls `sync()` first. Treat it as a preview.
- **The JIT and interpreter agree across the language's tested surface,** but
  concurrency (`spawn`/`sync`/`with`) is native-only: the interpreter refuses
  it, so it needs the JIT. File I/O and the other native `std` modules run on
  both back ends (`brass repl` included); only the browser playground, which
  cannot load plugins, lacks them.

## License

Mozilla Public License 2.0. See [`LICENSE`](LICENSE).
