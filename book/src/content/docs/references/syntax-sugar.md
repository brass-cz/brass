---
title: "Syntax sugar"
description: "What the language constructs desugar to: the Result behind fallibility, error traces, the Default model behind methods, and sum subtyping."
---

Several Brass constructs are specified as **syntax sugar** over ordinary
prelude types. The specification is type-level: a program behaves as if the
expansion had been written out, and a type error in the expansion is
reported normally. The compiler is free to implement the constructs natively
(and does), as long as nothing observable distinguishes the implementation
from the expansion. In particular the method model below is fully **erased**:
by the time a program is lowered, method calls are direct calls and none of
the implied fields exist.

## The `Result` behind fallibility

`Result` is an ordinary two-variant sum declared in `core/error.cz`:

```brass
type Result =
    | Ok {
        value
    }
    | Err {
        error
    }
```

Every fallibility construct is sugar over it:

- A return type `T!` is `Result<T, E>` with `E` inferred from the body's
  error sources (`infer!` leaves both sides inferred).
- `error(x)` calls the ordinary prelude function of that name (see
  [error traces](#error-traces)); its result is an `Err`.
- A bare `return v` in a fallible function wraps as `Ok { value: v }`; a
  `Result`-typed value flows whole.
- `expr!` matches the operand: the `Ok` payload is the expression's value,
  an `Err` returns from the enclosing callable unchanged, or aborts with a
  rendered trace at the program's top level or in the entry `main`.

The name `Result` resolves through normal scoping at each sugar site, so a
module may **shadow** it with its own declaration:

```brass
type Result =
    | Ok {
        value
    }
    | Err {
        error: string
    }

fun parse(x: int32) -> int32! {
    if x < 0 {
        // The module's Result: construct it directly. `error(..)` is a
        // prelude function and always builds the prelude's Result.
        return Result.Err { error: "negative" }
    }
    return x * 2
}
```

A shadowing declaration must have exactly the `| Ok { value } | Err { error }`
shape (payload annotations allowed; they pin the sugar's payload types);
anything else, and an alias named `Result`, is rejected at the declaration.
The shadow and the prelude's Result are distinct types: values of one are
not usable as the other.

## Error traces

`core/error.cz` defines the error value model:

```brass
type Location = { file: string, line: int32, col: int32 }
type Frame = { message: string, location: Location }
type Error = { value, location: Location, frames: Frame[] }
```

`error(value)` wraps its payload:
`Result.Err { error: Error { value: value, location: <call site>, frames: [] } }`.
`Result.context(self, ctx)` appends a `Frame` to a failed result and leaves a
success untouched. An unhandled `!` renders the trace through
`Error.display`, newest context first:

```brass
fun a() -> infer! {
    return error("error in a")
}

fun b() -> infer! {
    return a().context("error in b")
}

b()!
```

```text
[main.cz:6:12] unhandled error: error in b
    [main.cz:2:12] unhandled error: error in a
```

Two mechanisms make this work:

- **The implicit location parameter.** A callable whose _last_ parameter is
  annotated with the prelude `Location` record may be called without it; the
  compiler fills the argument with the call site's position. `error` and
  `context` declare one (`loc: Location`), which is how they know where they
  were called. The parameter is ordinary: visible in the signature, and a
  caller may pass it explicitly.
- **Error lifting at `!`.** A propagated payload that is not already an
  `Error` (a plugin's or builtin's plain string, for example) is re-raised
  wrapped into one, stamped with the propagation site. This is what lets one
  body mix `error(..)` with `!`-forwarded builtin failures. A chain that
  never touches `error(..)`/`context` and aborts directly keeps the plain
  `unhandled error: <payload>` form.

Two accepted deviations from the pure-sugar reading: `error` is reserved in
call position (a `match`'s `Err { error }` binding does not shadow the
function), and the checker types `error(..)` itself (each call's `Ok` payload
is taken from the position the call flows into) while the prelude body is
what runs.

## Methods are `Default` fields

`core/default.cz` declares the protocol type:

```brass
type Default = {
    default() -> Self
}
```

A type **satisfies** `Default` when it provides a `default()` method
producing its own default value. A method declaration is, semantically, a
field whose type satisfies `Default`:

```brass
type T = { x }
fun T.get(self) {
    return self.x
}
```

declares a member `get` on `T` whose function type's `default()` produces
the declared function, `(value) -> value.x`. In the model, `a.get` denotes
that function (a member absent from the value is materialized by its type's
`default()`), and a call `a.get()` applies it to the receiver: `(a.get)(a)`.
The model implies, and the implementation guarantees:

- A method member may be **absent from a value**: methods never affect
  structural subtyping, construction, layout, `fields(..)` iteration, or
  printing.
- A constructor cannot initialize it and code cannot assign it; the member
  is the declaration's, not the value's. (This is where the implementation
  is deliberately stricter than the model: allowing per-value overrides
  would make every method call a dynamic dispatch.)
- **Only method declarations get this treatment.** A user-declared field is
  an ordinary value field whatever its type: a field whose type satisfies
  `Default` is still required at every construction, and a structural
  subtype must provide every field.
- On a sum type, a method is present on every variant, which is also why a
  field shared by **all** variants of a sum may be read without a `match`:

```brass
type Shape =
    | Circle { r: int32, label: string }
    | Square { side: int32, label: string }

fun tag(s: Shape) -> string {
    return s.label
}
```

The built-in types satisfy `Default` with their zero values: `int32.default()`
is `0` (likewise every numeric width), `bool.default()` is `false`,
`string.default()` is `""`. An empty array is written as an annotated literal
(`let xs: T[] = []`).

An _uncalled_ member access `x.m` keeps its compile-time
[member-presence meaning](/references/reflection/#member-presence-xm-without-a-call) rather than
producing the method as a value. Every receiver supports the test (the
primitive classes, records, and sums alike), and a declared method reads as
present, so `if v.m { v.m() } else { ... }` dispatches on whether the
receiver's type implements `m`, and a presence-dispatching function
instantiates at scalars too.

## Declared sum subtyping

A sum may declare another sum as its parent. It must cover **exactly** the
parent's variant set, and each variant may only _widen_ the parent's variant
record (extra fields; annotated fields stay invariant):

```brass
type MyResult: Result =
    | Ok {
        value
        message
    }
    | Err {
        error
    }

fun a() -> infer! {
    return MyResult.Err { error: "message" }
}
```

At every flow site that accepts the child where the parent is required (a
`return`, a binding, an argument, a `!` operand), the value is **rebuilt** as
the parent: the extra width fields are dropped and the result is a new
value (identity and aliasing do not survive the coercion). Subtyping is
gated on the declaration; two structurally identical sums that do not
declare the relationship stay unrelated, and the relationship never
participates in unification, only in one-directional flow.

Because rebuild is the semantics, the parent's methods always run on parent
values; a child therefore does not need to (re)implement them, and only the
variant fields are checked for conformance.
