# Installing prepoly

Unfortunately, we don't provide pre-built binaries yet.
So here we describe how to build and install the prepoly command-line driver.

## Clone the repository

First, clone the prepoly source code:

```bash
git clone https://github.com/cordx56/prepoly.git
```

## Install the Rust compiler

prepoly is written in the Rust language.
So first you have to install the Rust compiler.

You can learn how to install Rust here: [https://rust-lang.org/tools/install/](https://rust-lang.org/tools/install/)

## Build prepoly with the native runtime

After installing Rust, you can build the default native driver:

```bash
./x cargo build --release
```

The script `x` builds the `bootstrap` crate and executes commands via the `bootstrap` binary.
The `bootstrap` binary downloads LLVM, which is required to use JIT compilation, and sets its path for the prepoly build.

The resulting binary `prepoly` is made under the `target/release` directory.

If you want the interpreter-only driver without LLVM, disable default features:

```bash
cargo build -p prepoly_driver --no-default-features
```

## Install prepoly

Run the following command to install the default native driver:

```bash
./x cargo install --path crates/prepoly_driver
```

Note that you have to add the path where the `prepoly` binary is placed to `$PATH`.
