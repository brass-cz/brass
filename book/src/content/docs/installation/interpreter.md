---
title: "Installing Brass"
description: "Package a complete Brass toolchain or build only the brass binary."
---

For a usable local installation, build the complete toolchain archive. Build
only the driver binary when you are working on the compiler itself.

## Clone the repository

First, clone the Brass source code:

```bash
git clone https://github.com/brass-cz/brass.git
cd brass
```

## Install the Rust compiler

Brass is written in Rust, so you need the Rust compiler installed first.

You can learn how to install Rust here: [https://rust-lang.org/tools/install/](https://rust-lang.org/tools/install/)

## Build the complete toolchain

The recommended build creates the same layout as a release:

```bash
./scripts/pack.sh
```

The script builds `brass`, `czls`, and `czfmt`, builds the standard-library
plugins, creates the `czpm` launcher, verifies the package manager, and writes
`brass-<host-target>.tar.gz` in the repository root. The archive contains a
ready-to-move `bin/` and `std/` tree; keep those directories together after
extracting it, and add `bin/` to `PATH`.

The `x` helper used by the script bootstraps the Rust build and downloads the
LLVM toolchain required by the default native runtime.

## Build only the `brass` binary

For compiler development, build the native driver directly:

```bash
./x cargo build --release -p brass_driver
```

The binary is written to `target/release/brass`. This command does not package
the standard library, `czpm`, the language server, or the formatter. In
particular, a repository build does not automatically resolve `import std.*`;
use the complete toolchain above for normal use.

To build an interpreter-only driver without LLVM:

```bash
cargo build --release -p brass_driver --no-default-features
```

## Usage

```bash
brass program.cz         # check the needed code and run it
brass check program.cz   # check the whole program; silent on success
brass repl program.cz    # run with the interpreter
brass                    # start an interactive REPL
```

An interactive session retains definitions and bindings between turns. Before
executing the new input, it validates that input together with the accumulated
session, but it does not execute earlier effectful statements again: prior
prints and `input()` calls are not repeated.

Diagnostics are printed to stderr and produce a non-zero exit status. A normal
run checks functions as it needs them; use `brass check` for a complete
whole-program result. See [Hello, world!](/guides/hello/#checking-without-running)
for the practical distinction.
