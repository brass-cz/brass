# Installing the prepoly interpreter

Unfortunately, we don't provide pre-built binaries yet.
So here we describe how to build and install the prepoly interpreter.

## Install the Rust compiler

The prepoly interpreter is written in the Rust language.
So first you have to install the Rust compiler.

You can learn how to install Rust here: [https://rust-lang.org/tools/install/](https://rust-lang.org/tools/install/)

## Build the prepoly interpreter

After installing Rust, you can build the prepoly interpreter:

```bash
./x cargo build --release
```

The script `x` builds the `bootstrap` crate and executes commands via the `bootstrap` binary.
The `bootstrap` binary downloads LLVM, which is required to use JIT compilation, and sets its path for the prepoly build.

The resulting binary `prepoly` is made under the `target/release` directory.

## Install the prepoly interpreter

Run the following command to install the prepoly interpreter:

```bash
./x cargo install --path crates/prepoly_driver
```

Note that you have to add the path where the `prepoly` binary is placed to `$PATH`.
