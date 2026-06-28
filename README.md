<div align="center">
  <h1>
    prepoly
  </h1>
  <p>
    Statically and flexibly type-inferred programming language
  </p>
  <p>
    and its interpreter implementation with JIT-compilation
  </p>
</div>

prepoly is a statically type-checked, structurally-typed programming language
with Hindley-Milner-style type inference, sum and record types under a single
`type` keyword, explicit interface contracts, nullable and `Result` error types,
closures, a file-based module system, and a small standard library written in
prepoly itself. The name is a contraction of *pre-typed* and *polymorphic*: it
is run like an interpreter, but every function is fully type-checked just before
it executes, and most types are inferred rather than written.

This repository is the reference implementation: a Rust + LLVM workspace that
lexes, parses, type-checks, monomorphizes, and then either **JIT-compiles**
each program to native code through LLVM or **interprets** it directly, backed
by a reference-counted runtime with a cycle collector and region-based
ownership for concurrency.

```
$ prepoly examples/02_sum_types.pp
result = 7
negate 5 = -5
color = green
```

## Architecture

One source program flows through the pipeline below. Every stage is a separate
crate; the cross-platform front and middle ends know nothing about the back end
that finally runs the program.

```
source
  -> prepoly_lexer     tokens: newlines, string interpolation, comments
  -> prepoly_parser    newline-aware recursive descent -> AST
  -> prepoly_hir       lower AST -> HIR, a typed program model with type ids
  -> prepoly_resolve   module imports, visibility, scopes
     prepoly_typeck    HM inference + structural subtyping, interfaces,
     prepoly_solver    exhaustiveness, nullable narrowing, const, flow
  -> prepoly_mir       lower each body to a *type-independent* control-flow
                       graph in three-address form (locals carry type
                       variables, not concrete types)
  -> prepoly_engine    monomorphize: concretize the type variables per call
                       instance into typed, unboxed instances, then drive a
                       backend-agnostic `Codegen` over them
  -> back end (chosen at this stage):
       prepoly_jit_llvm   typed unboxed LLVM IR (via inkwell) + OrcJIT  [default]
       prepoly_repl       tree-walking interpreter over the same MIR    [no LLVM]
  -> prepoly_runtime   pure-Rust C-ABI runtime linked into JIT-compiled code:
                       bump allocator, reference counting, a cycle collector,
                       regions/cowns, builtins, and file I/O
```

| Crate | Responsibility |
|-------|----------------|
| `prepoly_lexer` | `token.rs`, `lexer.rs` — tokens including newlines, `{expr}` interpolation, comments |
| `prepoly_parser` | `parser.rs`, `ast.rs`, `newline.rs` — newline-significant recursive descent |
| `prepoly_hir` | `lower.rs`, `hir.rs`, `types.rs`, `typed.rs` — typed program model, type ids, `Type` |
| `prepoly_resolve` | `module.rs`, `scope.rs`, `visibility.rs` — imports, `_`-privacy, scopes |
| `prepoly_solver` | `solver.rs`, `unify.rs` — the HM unification engine shared by the type checker |
| `prepoly_typeck` | `infer.rs`, `hm.rs`, `structural.rs`, `interface.rs`, `exhaustive.rs`, `narrow.rs`, `constck.rs` — all static checks |
| `prepoly_mir` | `lower/`, `cfg.rs`, `builder.rs`, `analysis.rs` — type-independent control-flow IR |
| `prepoly_engine` | `mono.rs`, `mir_infer.rs`, `codegen.rs`, `engine.rs` — monomorphization + the backend-agnostic codegen interface |
| `prepoly_jit_llvm` | `codegen.rs`, `layout.rs`, `closure.rs`, `dispatch.rs`, `ownership.rs`, `jit/` — LLVM IR + JIT execution |
| `prepoly_repl` | `interp.rs`, `value.rs`, `format.rs` — the no-LLVM interpreter back end |
| `prepoly_runtime` | `alloc.rs`, `mem.rs`, `gc.rs`, `region.rs`, `conc.rs`, `builtins.rs`, `io.rs`, `rt.rs` — the C-ABI runtime |
| `prepoly_driver` | `main.rs` — the `prepoly` CLI: module graph, checks, back-end selection |
| `bootstrap` | the `./x` runner — downloads LLVM and runs cargo with it on the path |

The source comments are the canonical documentation for each crate. An
introductory tutorial lives in [`book/`](book/) (mdBook).

## Building

The native build with the LLVM JIT links **LLVM 22.1.0** statically. Rather than
require a system LLVM, the repository ships a small `bootstrap` tool, invoked
through the `./x` wrapper, that downloads a prebuilt LLVM 22.1.0 into `./llvm/`
on first use (Linux and macOS, x86-64 and ARM64), points `LLVM_SYS_221_PREFIX`
at it, and then execs the command you gave it. Use `./x` in place of `cargo`:

```sh
./x cargo build --release        # downloads LLVM on first run; -> ./target/release/prepoly
./x cargo test --workspace
./x cargo clippy --workspace --all-targets
```

LLVM is needed only by the JIT back end and its runtime. The rest of the
toolchain is pure Rust and builds with plain `cargo`, so you can work on the
front/middle ends, or run an interpreter-only build, without any LLVM:

```sh
cargo test -p prepoly_typeck                        # any portable crate, no ./x
cargo build -p prepoly_driver --no-default-features # native driver, interpreter only
```

The workspace's default members are exactly the cross-platform crates, so a
plain `cargo build`/`cargo test` and a wasm build operate on the portable set
without dragging in LLVM. (`./x cargo test --workspace` additionally builds and
tests the LLVM crates as part of the JIT.)

### WebAssembly (wasm32-wasip1)

prepoly also builds for `wasm32-wasip1`, where the LLVM JIT cannot link. The
driver's `build.rs` detects a wasm target and turns the default `jit` feature
off, so the LLVM dependencies are never pulled in and the program runs through
the pure-Rust interpreter back end (`prepoly_repl`) instead.

```sh
cargo build --target wasm32-wasip1 -p prepoly_driver
wasmtime run --dir=. target/wasm32-wasip1/debug/prepoly.wasm run program.pp
```

The interpreter covers the typed sequential subset (scalars, strings, arrays,
records, sum types, closures, nullable/`Result`, control flow, recursion).
Constructs outside that subset — concurrency, file I/O, and deferred type
dispatch — report a clear error rather than executing.

## Running programs

```sh
prepoly       path/to/file.pp     # type-check and run (the LLVM JIT when available)
prepoly check path/to/file.pp     # type-check only, print "ok"
prepoly repl  path/to/file.pp     # run a file through the interpreter
prepoly repl                      # start an interactive interpreter session
prepoly                           # no arguments: same interactive session
```

A bare file argument is type-checked and run; it uses the LLVM JIT when it is
available — the default `jit` feature on a non-wasm target — and otherwise falls
back to the interpreter. The two back ends share the entire front end, so they
accept and reject exactly the same programs. `repl` always uses the interpreter.

A program runs each module's top-level statements in dependency order and then
calls `main` if it is defined. The standard library is an implicit prelude, so
`map`, `split`, `sqrt`, and friends are available without an import.

### Interactive REPL

Running `prepoly` (or `prepoly repl`) with no file starts an interactive
session driven by the interpreter. Top-level definitions (functions, types,
imports) accumulate, and statements and expressions run inside an implicit
`main`. Because the interpreter is deterministic, the session re-runs the
accumulated history each turn and prints only the newly produced output; a bare
expression is echoed by wrapping it in `println`. Errors do not end the session:
the offending input is rolled back and the diagnostic is shown. An item spanning
multiple lines keeps reading while its braces are unbalanced.

```
$ prepoly
prepoly REPL -- enter definitions or statements; Ctrl-D to exit.
> 1 + 2 * 3
7
> let x = 10
> fun sq(n) { return n * n }
> sq(x)
100
> [1, 2, 3].map((n) -> n * 10)
[10, 20, 30]
```

Run every bundled example with its output:

```sh
./run_examples.sh
```

## Language tour

### Records and sum types

`type` defines both records (structs) and sum types (tagged unions). A member
with `(params)` after its name is a method; one without is a field. A method
whose first parameter is `self` is an instance method, otherwise it is static.

```
type Account = {
    owner: string
    balance: int32

    open(owner: string) -> Account {     // static: Account.open(...)
        return Self { owner: owner, balance: 0 }
    }
    deposit(self, amount: int32) {       // instance: acc.deposit(...)
        self.balance += amount
    }
}

type Shape =
    | Circle { radius: float64 }
    | Rectangle { width: float64, height: float64 }
    | Point
```

### Pattern matching

`match` over a sum type is checked for exhaustiveness. `if let` matches a single
variant. Literal and wildcard patterns and fixed-length array destructuring are
supported.

```
fun area(s: Shape) -> float64 {
    return match s {
        Circle { radius } => 3.14159 * radius * radius,
        Rectangle { width, height } => width * height,
        Point => 0.0,
    }
}

let [first, second] = [10, 20]
```

### Interfaces (contracts without inheritance)

`type B: A` requires `B` to provide every field and method of `A`, checked at
compile time. No implementation is inherited. Plain structural subtyping lets a
function accept any value that has the members it uses.

```
type Showable = { to_string(self) -> string }

type User: Showable = {
    name: string
    to_string(self) -> string { return self.name }
}

fun print_info(obj) { println(obj.to_string()) }   // accepts anything Showable
```

### Nullable and Result

`T?` is a nullable type narrowed by `if`. `Result` is built in: `error(x)`
constructs an error, and `expr!` propagates one by returning early. A fallible
function with no return annotation wraps plain returns in `Result.Ok`.

```
fun parse_positive(s: string) {
    let n = int32.parse(s)!            // returns early on failure
    if n < 0 { return error("negative") }
    return n                           // wrapped in Result.Ok
}

let x: int32? = first_even(nums)
if x { println("got {x}") }            // x is int32 inside the guard
```

### Closures

Closures capture their environment by reference, so captured variables remain
shared and mutable.

```
fun make_accumulator(initial: int32) {
    let total = initial
    return (amount: int32) -> {
        total += amount
        return total
    }
}
```

### Strings, operators, conversions

Strings interpolate with `{expr}`. There is no implicit numeric conversion;
mixing `int32` and `float64` is an error, and conversions are explicit.

```
let name = "world"
println("hello {name}")
let f = float64.from(n) + 0.5
let i = int32.parse("123")!
```

### Modules

One file is one module; the directory layout is the module path. Public names
(no leading `_`) can be imported. An import path is resolved relative to the
directory of the file that contains it, so a module imports a sibling by its bare
name.

```
// main.pp        ->  import modules.a.{ a }
// modules/a.pp   ->  import b.{ b }     // resolves to modules/b.pp, a's sibling
// modules/b.pp
import geometry.vec.{ Vec2, dot }
```

### Concurrency

The only concurrency primitives are `spawn(f)` and `with(cown, f)`; ownership
(move/freeze/cown) is inferred by the compiler and never written by the
programmer. See [Status and limitations](#status-and-limitations) for the
current execution model.

```
spawn(() -> { for n in nums { counter.add(n) } })
with(counter, (c) -> { println("total = {c.total}") })
```

## Examples

Every language feature is covered by a runnable example in
[`examples/`](examples/), each verified by `cargo test`:

| File | Features |
|------|----------|
| `01_records.pp` | records, static/instance methods, `Self`, `const` |
| `02_sum_types.pp` | sum types, nested match, recursion, unit variants |
| `03_interfaces.pp` | multi-interface enforcement, structural subtyping |
| `04_sum_interface.pp` | interface enforcement over every variant |
| `05_nullable_and_result.pp` | `T?` narrowing, `Result`, `error`, `!` |
| `06_structural_subtyping.pp` | duck-typed functions, deferred dispatch |
| `07_closures.pp` | mutable capture, method chains, line continuation |
| `08_pattern_matching.pp` | exhaustive match, literals, wildcard, `if let` |
| `09_collections.pp` | `map`/`filter`/`fold`/`sort`, math helpers |
| `10_strings_and_conversions.pp` | string library, numeric conversions |
| `11_control_flow.pp` | `while`/`for`/`break`/`continue` |
| `12_concurrency.pp` | `spawn` / `with` |
| `13_file_io.pp` | file read/write returning `Result` |
| `14_type_safety.pp` | static type-safety checks and nullable narrowing |
| `15_numeric_conversions.pp` | fallible numeric conversions and range errors |
| `16_method_inference.pp` | inferred method/function return types |
| `17_higher_order.pp` | closures as arguments, shadowing-safe calls |
| `18_ufcs.pp` | UFCS method-call resolution with receiver typing |
| `modules/main.pp` | cross-file `import` |

The `e2e_tests/` directory holds additional source/expected-output pairs that
the back ends are checked against, and the example and module integration tests
run each program through the JIT and assert its output.

## Implementation

### How execution works

After the front end produces a checked program, `prepoly_mir` lowers each
function, method, module-init, and closure body **once** into a control-flow
graph in three-address form. This MIR is deliberately *type-independent*: its
locals carry type variables, so the control-flow shape is built a single time
regardless of how many concrete types eventually flow through it.

`prepoly_engine` then performs **true monomorphization**. Starting from the
entry points it walks the call graph and, for each `(callable, concrete
argument types)` it reaches, concretizes the MIR's type variables and emits one
specialized, fully typed instance. Every value in a monomorphized instance has a
concrete type, so the back end emits **unboxed** code — there is no uniform
tagged value. The same `MonoProgram` of typed instances feeds either back end
through the engine's `Codegen` trait:

- **The LLVM JIT** (`prepoly_jit_llvm`) implements `Codegen` by emitting typed
  LLVM IR — native control flow, arithmetic, and calls over concrete LLVM types
  and struct layouts (`layout.rs`) — and runs the module through LLVM's OrcJIT.
- **The interpreter** (`prepoly_repl`) walks the same monomorphized MIR
  directly. It needs no native code generation, so it is the back end on wasm
  and for the `repl` subcommand.

The rare operation whose type genuinely cannot be pinned at compile time (a
value crossing a structural/deferred-dispatch boundary) is resolved through a
small runtime trampoline (`dispatch.rs`), which realizes the design's *deferred*
monomorphization.

### Heap objects and memory management

Scalars are unboxed registers. Heap objects — strings, records, sum variants,
arrays, closures, and cowns — are each prefixed with a 16-byte header
(`prepoly_runtime::rt::Header`: a reference count, an owner class, an object
kind, and region/GC metadata bytes). The typed back end lays out each object's
body itself and accesses fields by direct offset.

- **Reference counting** is maintained by the generated code. An object's
  `owner` class selects its behavior: the three *owned* classes (Local,
  Contained, Bridge) use a non-atomic count, and the two *shared* classes
  (Immutable, Cown) use an atomic one.
- **The cycle collector** in `prepoly_runtime::gc` is a trial-deletion
  (Bacon–Rajan) collector over the objects that can form cycles.
- **Closures** capture their environment by boxing captured locals into heap
  cells shared between the enclosing scope and the closure, so the
  accumulator/counter examples mutate captured state across calls.
- **Concurrency** (`spawn`/`with`) runs on the region-ownership runtime. The
  compiler's automatic move/freeze/cown analysis (`prepoly_jit_llvm::ownership`)
  decides how each `spawn` capture is shared and reports a note when a capture
  is auto-wrapped in a cown.

### Static checks

Interface conformance, match exhaustiveness, `const`, unknown type names,
nullable narrowing, and the no-implicit-int/float-conversion rule all run in the
type checker before any code is generated. Monomorphization re-checks each
concrete instance, so the typed back ends only ever see well-typed, fully
concrete bodies.

## Status and limitations

Sequential execution is the tested, supported path: the workspace builds clean
under `clippy` and its test suite (over 400 tests, including the JIT integration
suites) passes. A few sharp edges are worth knowing:

- **Concurrency is experimental.** `spawn` runs a closure on a real OS thread.
  Each capture shared with the thread is promoted before the spawn — a read-only
  capture is frozen, a mutated one is made a cown — so its reference count is
  atomic, and the cycle collector is deferred while any spawned thread runs, so
  the heap stays race-free. Scheduling is not yet structured, though: spawned
  work runs asynchronously and is joined only at the end of `main`, so a read
  that races ahead of the spawned tasks can observe incomplete results — call
  `sync()` to wait for them first.
- **The interpreter and JIT are close but not byte-for-byte identical.** Both now
  trap integer division by zero and out-of-bounds array indexing, but a few edges
  still differ (for example over-width bit shifts), so a program that leans on
  such corner cases may behave differently across the two back ends.
- **There is no separate design document.** Earlier revisions referred to a
  `DESIGN.md`/`PLAN.md`; the source comments are now the single source of truth,
  and some comments still cite those removed files by section number.

## License

Mozilla Public License 2.0. See [`LICENSE`](LICENSE).
