---
title: "Syntax"
description: "The complete surface syntax: lexical rules, operators, statements, patterns, declarations, and type expressions."
---

This chapter describes the surface syntax exhaustively. Source files use the
`.cz` extension; one file is one module (see [Modules](/references/modules/)).

## Lexical structure

### Comments

```brass
// a line comment, to the end of the line
#  a line comment as well
/* a block comment
   /* which may nest */
   still a comment */
```
Block comments nest: each `/*` must be closed by its own `*/`. A newline
inside a block comment does not separate statements; a newline that ends a
line comment does. `//` and `#` are interchangeable; because `#` starts a
line comment, a file may begin with a shebang line
(see [Hello, world!](/guides/hello/#running-as-a-script)):

```brass norun
#!/usr/bin/env brass
```
### Doc comments

A block comment that opens with `/**` is a **documentation comment**. Written
directly above a `fun` or `type` declaration, it attaches to that declaration
and is shown by editor tooling: the [language server](/installation/lsp/)
renders it on hover and in completion, below the signature:

```brass
/** The area of a circle with radius `r`. */
fun area(r: float64) -> float64 {
    return 3.14159 * r * r
}

/**
 * A named point on the screen.
 * Coordinates are pixels.
 */
type Point = {
    x: int32
    y: int32
}

println(area(2.0))
```
The text is the comment body with the `/**` and `*/` markers and each line's
leading `*` decoration removed; it is treated as markdown. Attachment rules:

- The doc comment must sit directly above the declaration: only line breaks
  and ordinary comments may come between. Several stacked doc comments join
  into paragraphs.
- Doc comments attach to `fun` (including method implementations
  `fun T.m(...)`) and `type` declarations only. One written above anything
  else, such as a top-level `let`/`const`, an import, or a member signature
  inside a type body, is ignored like an ordinary comment.
- A plain `/* ... */` (single asterisk) is never a doc comment, and the empty
  `/**/` is a plain comment.

Doc comments have no runtime presence; they exist for readers and tooling.
The standard library documents its public functions and types this way.

### Identifiers and keywords

An identifier starts with an ASCII letter or `_` and continues with ASCII
letters, digits, or `_`. Unicode identifiers are not supported. A lone `_` is
the wildcard pattern.

The reserved keywords are:

```
type fun let const if else match for while in
return break continue null true false self Self import
```
Everything else is an ordinary identifier. In particular `ref`, `mut`,
`infer`, `typeof`, `anonymous` are recognized contextually in type position;
`spawn`, `with`, `sync`, `error`, `print`, `println`, `len`, `open`, `assert`
are functions (the builtin ones cannot be redefined); and there is no `loop`,
`defer`, `pub`, `impl`, or `trait`.

### Integer literals

Decimal by default, with radix prefixes and `_` separators:

```brass
let a = 1_000_000
let b = 0xFF        // hex (0x / 0X)
let c = 0b1010      // binary (0b / 0B)
let d = 0o755       // octal (0o / 0O)
```
There are no type suffixes: the type of a literal is decided by inference
(see [Type system](/references/types/#literals)). A literal too large for `int64` is a
lexing error.

### Float literals

A float literal requires a digit after the decimal point (`1.0`, not `1.`),
and accepts an exponent and `_` separators: `6.02e23`, `1_0.5`. Because a
float needs a digit after `.`, `42.foo` lexes as the integer `42` followed by
a field access. There are no float suffixes, and radix prefixes do not apply
to floats.

### String literals and interpolation

Strings are double-quoted UTF-8. The recognized escapes are:

```
\n  \t  \r  \0  \\  \"  \{  \}
```
Any other escape is an error. `{expr}` inside a string is **interpolation**:
the expression is evaluated and its text inserted. Literal braces are written
`\{` and `\}` (there is no `{{` doubling). The interpolation scanner balances
nested braces and skips nested string literals, so an interpolated expression
may itself contain strings and braces:

```brass
let items = ["a", "b"]
println("first = {items[0]}, count = {items.len()}")
```
There is no character type (a character is a one-character string) and no
raw or multi-line string form (use `\n`).

### Statements and newlines

Newlines separate statements; there are no semicolons (`;` is not a token). A
line _continues_ onto the next in these cases:

- the line ends with a binary or assignment operator;
- the next line begins with `.` (method chain);
- an `else` begins the next line after an `if` block;
- inside parentheses `()`, brackets `[]`, and the braces of record literals,
  `match` bodies, and type bodies, newlines are insignificant.

```brass
let total = 100 *
    2 +
    50

let result = [3, 1, 4]
    .map((x) -> x * 10)
    .fold(0, (a, b) -> a + b)
```
Commas are optional between type members and between match arms (newlines
separate just as well), and trailing commas are accepted in every
comma-separated list (arguments, parameters, array literals, field lists,
imports, patterns).

## Operators

From lowest to highest precedence; all binary operators are left-associative:

| Precedence   | Operators                   | Meaning                                        |
| ------------ | --------------------------- | ---------------------------------------------- |
| 1 (lowest)   | `\|\|`                      | logical or                                     |
| 2            | `&&`                        | logical and                                    |
| 3            | `==` `!=` `<` `<=` `>` `>=` | comparison                                     |
| 4            | `\|`                        | bitwise or                                     |
| 5            | `^`                         | bitwise xor                                    |
| 6            | `&`                         | bitwise and                                    |
| 7            | `<<` `>>`                   | shifts                                         |
| 8            | `+` `-`                     | additive                                       |
| 9            | `*` `/` `%`                 | multiplicative                                 |
| 10           | `-x` `!x` `~x`              | prefix: negation, logical not, bitwise not     |
| 11 (highest) | `x.f` `f(args)` `x[i]` `x!` | postfix: field, call, index, error propagation |

Notes:

- Postfix `!` is [error propagation](/references/types/#result). There is **no** postfix
  `?` operator and no optional chaining (`?.`); `?` appears only as the
  nullable _type_ suffix.
- Assignment is a statement, not an expression. The assignment operators are
  `=` `+=` `-=` `*=` `/=` `%=`; there are no bitwise or shift compound
  assignments. The target may be a variable, a field (`a.b`), or an element
  (`a[i]`).
- There is no general range operator. The bracket form `[lo..hi]` is an
  _expression_ producing the half-open integer range `lo .. hi-1` as an array:
  `[1..5]` is `[1, 2, 3, 4]`.

## Expressions

- **Literals**: integers, floats, strings, `true`, `false`, `null`.
- **Array/tuple literal** `[a, b, c]`: how a bracket literal is typed (fixed
  array, growable array, or tuple) is described in the
  [type system](/references/types/#bracket-literals).
- **Record construction** `TypeName { field: value, ... }`,
  `Self { ... }` inside methods, and variant construction
  `Type.Variant { ... }` (a unit variant is `Type.Variant` with no braces).
- **Anonymous record literal** `{ field: value, ... }`: a structural record
  with no declared type. At statement position an opening `{` starts a block;
  the literal form is recognized by the `name:` lookahead.
- **`if` / `else`** is an expression and yields a value; `else if` chains.
  The condition does not take a record literal directly (parenthesize if
  needed).
- **`if let`** `if let PATTERN = expr { ... } else { ... }` matches one
  pattern; on a nullable scrutinee, a bare name pattern binds the non-null
  value.
- **`match`** is an expression:

  ```
  match scrutinee {
      pattern => expression,
      pattern => { block },
      pattern => target = value,   // an assignment arm is allowed
  }
  ```
  Arms are separated by commas or newlines. There are no match guards.

- **Closures** `(params) -> expr` or `(params) -> { block }`. Parameter
  annotations are optional; zero parameters are written `()`. A block body
  yields a value only through `return`; an expression body yields the
  expression. A `(` opens a closure exactly when its matching `)` is followed
  by `->`.
- **Calls, indexing, field access** as usual: `f(a, b)`, `xs[i]`, `p.x`.
  Method calls are `recv.method(args)`; static methods are
  `Type.method(args)`.

Expression nesting is capped (currently 150 levels) to report a diagnostic
instead of overflowing the parser stack.

## Statements

The complete statement list: `let`/`const`, assignment, expression statement,
`while`, `for`, `return`, `break`, `continue`.

### `let` and `const`

```brass norun
const pi = 3.14159        // immutable binding
let count = 0             // mutable binding
let x: int64 = 10         // with a type annotation
let [a, b] = [10, 20]     // destructuring (array/tuple pattern)
let p: Point              // uninitialized: `let` + annotation only
```
`const` requires an initializer. An unannotated `let` requires an
initializer. An annotated `let` may omit it; the binding must then be
definitely assigned before use (see
[definite assignment](/references/types/#definite-assignment)).

### Loops

```
while cond { ... }
for x in xs { ... }        // arrays and [lo..hi] ranges
break
continue
```
The `for` head takes a single variable name (no destructuring). `break` and
`continue` are bare; there are no labels.

### `return`

`return` with no value returns `void`; `return expr` returns the value. In a
fallible function a plain value is wrapped in `Result.Ok` automatically (see
[Result](/references/types/#result)).

## Patterns

Patterns appear in `match` arms, `if let`, and `let` destructuring:

| Pattern          | Example                                           | Notes                                                                          |
| ---------------- | ------------------------------------------------- | ------------------------------------------------------------------------------ |
| Wildcard         | `_`                                               | matches anything, binds nothing                                                |
| Binding          | `x`                                               | binds the whole value; also matches a unit variant of that name                |
| Literal          | `0`, `-5`, `1.5`, `"s"`, `true`, `null`           | negative numeric literals allowed                                              |
| Variant / record | `Circle { radius }`, `Shape.Circle { radius: r }` | field shorthand binds the field name; `field: subpattern` destructures further |
| Rest             | `Full { data, .. }`                               | `..` ignores the remaining fields                                              |
| Array            | `[a, b]`                                          | fixed length; no `..` rest inside arrays                                       |

There are no or-patterns (`|`), no `@` bindings, and no range patterns.
`match` over a sum type must be exhaustive (see
[exhaustiveness](/references/types/#match-exhaustiveness)).

## Declarations

### Functions

```
fun name(param, other: Type, third: ref(mut(T))) -> ReturnType {
    ...
}
```
Both parameter and return annotations are optional. `fun T.m(params)` declares
a method of type `T` (see [methods](/references/types/#methods)); the standard library
also uses the receiver forms `fun string.m`, `fun int32.m` (any primitive type
word), `fun infer[].m`, and `fun string[].m` to put methods on primitive and
array types (user code cannot).

### Types

```brass norun
type Name = { members }                  // record
type Name = | V1 { members } | V2       // sum type
type Name: IfaceA, IfaceB = { members } // with interface constraints
type Child: Parent = | V1 { .. } | V2   // sum with a declared parent (subtyping)
type Alias = Base { field: T, ... }     // refinement alias (see below)
```
A member is either a **field** (`name` or `name: Type`, the annotation is
optional), a **type slot** (`name: type`, a type parameter with no storage,
see [Type slots](/references/types/#type-slots-and-refinements)), or a **method
signature** (`name(params) -> Ret` with no body). A method body inside a `type`
block is a parse error: implementations go outside the type, as `fun T.m(...)`,
in the same module. Members are separated by commas or newlines.

Variants of a sum type are `Name` or `Name { members }`, separated by `|`,
which may start a new line. A leading `|` is optional for a sum with two or
more variants but **required** for a one-variant sum (`type X = | Only { .. }`),
so that `type Alias = Base { .. }` reads as a refinement rather than a
one-variant sum. A right-hand side that is a plain type expression (a
refinement, or any type) declares an **alias**: the name resolves to that type
and is not a new nominal.

### Imports

```brass norun
import geometry.vec.{ Vec2, dot }           // named imports
import geometry.vec.{ dot as vdot }        // rename a name
import geometry.vec.Vec2                    // one name, same as .{ Vec2 }
import geometry.vec                         // whole module: vec.dot(..), vec.Vec2
import geometry.vec as g                   // module with custom qualifier: g.dot(..)
```
`import path.{ Name, ... }` imports the listed names (`Name as Local` renames);
`import path.Name` imports the one trailing name; a bare `import path` imports
the module, whose exports are then used qualified by the path's last segment
(`vec.Vec2`, `vec.dot(a, b)`). `import path as name` overrides the qualifier.
See
[Modules](/references/modules/) for how the brace-less forms are
distinguished, path resolution, and visibility.

### Top level

A module is a sequence of imports, `type` declarations, `fun` declarations,
and bare statements, in any order. Functions and types may be referenced
before their textual definition; a top-level _binding_ may not (using a global
before its initializer runs is a compile error). Top-level statements execute
in order when the module loads; `main`, if defined, runs afterwards.

Top-level statements may use the `!` operator: a failed propagation stops
the program with the error instead of returning a Result (see
[Result](/references/types/#result)).

## Type expressions

Base forms:

| Form                         | Meaning                                                                                                      |
| ---------------------------- | ------------------------------------------------------------------------------------------------------------ |
| `int32`, `Point`, ...        | named type (primitives are ordinary names)                                                                   |
| `infer`                      | an inferred hole; each occurrence is independent                                                             |
| `[T, U, ...]`                | tuple                                                                                                        |
| `(T, U) -> R`                | function/closure type                                                                                        |
| `Self`                       | the enclosing type, in methods                                                                               |
| `mut(T)`                     | mutable value (deep copy in parameter position)                                                              |
| `ref(T)`                     | immutable reference                                                                                          |
| `ref(mut(T))`                | mutable reference (writes through)                                                                           |
| `typeof(expr)`               | the static type of `expr` (see [Reflection](/references/reflection/))                                        |
| `anonymous { name: T, ... }` | inline structural record type                                                                                |
| `type`                       | a type slot, only as a whole field's type (a type parameter)                                                 |
| `Self.field`                 | the type of the enclosing type's field/slot named `field`                                                    |
| `Base { field: T, ... }`     | a refinement pinning `Base`'s slots/fields (see [Type slots](/references/types/#type-slots-and-refinements)) |

Suffixes, applicable repeatedly and in any order:

| Suffix | Meaning                                               |
| ------ | ----------------------------------------------------- |
| `T[]`  | growable array (slice)                                |
| `T[n]` | fixed-length array (n a non-negative integer literal) |
| `T?`   | nullable                                              |
| `T!`   | Result with success payload `T`                       |

So `int32?[]` is an array of nullable int32, `int32[]?` a nullable array, and
`infer?[]`, `ref(mut(int32[]))`, `(int32) -> int32?` combine as expected.

The primitive named types are `int8`, `int16`, `int32`, `int64`, `uint8`,
`uint16`, `uint32`, `uint64`, `float32`, `float64`, `bool`, `string`, and
`void` (the no-value return type).
