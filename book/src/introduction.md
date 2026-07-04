# Introduction

**prepoly** is a programming language that requires only minimal type annotations and compiles programs just in time.

The name comes from *pre-typed* and *polymorphic*.
prepoly is an interpreted language that JIT-compiles your programs as it runs them, yet it checks types just before each function is executed.
You don't have to wait for compilation, but you still get the full benefit of type checking.

prepoly's type system is built on Hindley-Milner type inference, which reduces the burden of writing type annotations.
You can still add annotations explicitly to constrain the types of variables when you want to.

Features are summarized as follows:

- Just-in-time compilation
- Per-function type checking, performed just before each function runs
- Type inference for most types, resolved at execution time
- Structural subtyping with interface definitions

This book is organized in two parts: the **user guide** introduces the
language feature by feature, with runnable examples, and the **references**
describe the language exhaustively — the exact syntax, the type system rules,
the standard library, and the execution model.

## Playground

You can try prepoly on your browser:

<div>
  {{#include playground/introduction.html}}
</div>

You can use [full-screen playground](playground/index.html).
