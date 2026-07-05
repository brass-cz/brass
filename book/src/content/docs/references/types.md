---
title: "Type system"
description: "The type system in full: literals, conversions, parameter passing, structural typing, nullable, Result, and inference."
---

prepoly is statically typed with Hindley-Milner type inference. The whole
program is checked before anything runs; annotations constrain, they are never
required for safety. Polymorphic functions are checked again at each call site
with the actual argument types and compiled per concrete instantiation
(monomorphization), which is what lets most code omit annotations without
losing precision.

## Primitive types

| Kind              | Types                              |
| ----------------- | ---------------------------------- |
| Signed integers   | `int8` `int16` `int32` `int64`     |
| Unsigned integers | `uint8` `uint16` `uint32` `uint64` |
| Floats            | `float32` `float64`                |
| Other             | `bool` `string` `void`             |

`void` is the no-value return type. There is no character type — a character
is a one-character `string`. Error diagnostics may additionally mention
`never` (the type of `null` before it meets a context, spelled `never?`); it
is not writable in source.

## Literals

- The default type of an integer literal is `int32` when the value fits,
  otherwise `int64` (so `9223372036854775807` is an `int64`).
- The default type of a float literal is `float64`.
- A literal _adapts_ to an annotated type when it fits: `let b: int8 = -128`
  is fine, `let b: int8 = 300` is a compile error (never a silent wrap). A
  float literal adapts to either float width; an integer literal in a float
  context becomes a float.
- The required type can also come from a container the value flows into: a
  bare integer literal passed to a method of a map whose value type is pinned
  to `int64` (by a first store or a refinement annotation) is checked against
  `int64`, so it types as `int64` rather than defaulting to `int32` (and an
  `int32` value widens at the call).
- `INT64_MIN` cannot be written as one literal (`-9223372036854775808`
  overflows before the minus applies); the prelude constant exists instead.

### Bracket literals

A bracket literal `[...]` is typed in this order:

1. A type annotation (or another inference result, such as the parameter it is
   passed to) decides: the literal takes that type.
2. Elements that cannot unify make it a **tuple** — but a `null` element never
   does: `null` unifies with any element type, so `[4, null, 65]` is a
   sequence of `int32?`.
3. Bound immutably (`const`), it is a **fixed-length array**:
   `const a = [1, 2, 3]` is `int32[3]`.
4. Bound mutably (`let`) or in any other position, it is a **growable array**:
   `let a = [1, 2, 3]` is `int32[]`.

A fixed-length array is usable where a growable array of the same element is
required (the length is extra static information), but not the reverse.
`[lo..hi]` builds the half-open integer range as an array.

## Numeric conversions

### In operators

An arithmetic or comparison operator between two numeric values of different
types implicitly converts both operands to their **common type**: the smallest
type both convert to value-preservingly. So `int32 + int64` is `int64`,
`uint8 + int32` is `int32`, and `int32 + float64` is `float64`. Pairs with no
value-preserving common type (`int64` with `uint64`, `int64` with `float64`)
are a compile error; convert one side explicitly. `+` on two strings
concatenates.

### Flow conversions

Numeric values also convert automatically when they _flow_ into a numeric
position of another type — an assignment, an argument, a return value, a
compound assignment, or an element/field store — but only when the conversion
is **value-preserving**:

- an integer into a strictly wider integer of the same signedness;
- an unsigned integer into a strictly wider signed integer;
- `float32` into `float64`;
- an integer into a float whose mantissa holds every value exactly: up to
  `int32`/`uint32` for `float64`, up to `int16`/`uint16` for `float32`.

So `let b: int64 = an_int32` and `total += an_int32` (with `total: int64`)
both widen the value. Anything lossy — a narrower integer, a sign change, a
narrower float, `int64` into `float64`, or float into int — never happens
implicitly; the error suggests the explicit conversion.

A `T` value also flows freely into a `T?` position. A nullable value never
flows into a non-nullable one — it must be narrowed first.

### Explicit conversions

| Conversion                        | Result    | Notes                                                                            |
| --------------------------------- | --------- | -------------------------------------------------------------------------------- |
| `intN.from(x)`                    | `intN!`   | range-checked; `Err` when out of range                                           |
| `intN.parse(s)`                   | `intN!`   | parses a string                                                                  |
| `floatN.from(x)`                  | `floatN`  | **total** — always succeeds, precision loss is accepted because it was asked for |
| `floatN.parse(s)`                 | `floatN!` | parses a string                                                                  |
| `string.from(x)`                  | `string`  | total; renders any value                                                         |
| `T.from(v)` for a record type `T` | `T?`      | structural conversion — see [below](#structural-conversion)                      |

Note the asymmetry: `int32.from(3.9)` can fail (and truncates toward zero on
success), so it returns a Result; `float64.from(big_int64)` cannot fail, so it
returns a plain float even though it may round. The prelude also provides free
function aliases (`int32_from`, `int32_parse`, `float64_from`,
`float64_parse`, `string_from`).

## Parameter passing

How an argument is passed is part of the signature, and it is inferred when
not annotated:

| Annotation                | Passing                               | Callee mutation                                             |
| ------------------------- | ------------------------------------- | ----------------------------------------------------------- |
| _(none, body only reads)_ | shared reference                      | rejected by inference (would reclassify)                    |
| _(none, body mutates)_    | **private deep copy** at callee entry | stays local, invisible to the caller                        |
| `ref(T)`                  | immutable reference                   | rejected                                                    |
| `ref(mut(T))`             | mutable reference                     | **writes through** to the caller                            |
| `mut(T)`                  | mutable deep copy                     | stays local                                                 |
| `infer`                   | read-only deep copy                   | rejected — mutating an `infer` parameter is a compile error |
| _(numeric type)_          | by value                              | n/a — numbers are copied                                    |

Details:

- "Mutates" means a field or element store, a growing method (`push`,
  `insert`, `remove`, `pop`), a loop-variable write-back, or passing the value
  on into a position known to mutate. Rebinding the parameter name (`p = ...`)
  is not a mutation of the caller's value.
- The deep copy happens at **callee entry**, once, driven by the parameter's
  type.
- `ref(mut(T))` also requires the _argument_ to be mutable (`let`, not
  `const`), even if the body does not currently mutate it.
- `infer` may be combined structurally: `infer[]` requires "an array, element
  type inferred"; `infer?[]` an array of nullables. Each occurrence of `infer`
  is an independent inference hole.

### `self`

The `self` receiver is a special case: unannotated `self` is always a
_reference_. A method that only reads `self` receives `ref(Self)`; one that
mutates it receives `ref(mut(Self))`, so the change is visible to the caller.
Annotate `self: Self` to work on an owned deep copy instead (mutations stay
local).

### Optional trailing parameters

A trailing parameter of nullable type may be omitted at the call; it defaults
to `null`. The prelude's `assert(cond, msg: string?)` is callable as
`assert(cond)`.

## Records and structural typing

`type Name = { fields... }` declares a nominal record type. A field without a
type annotation accepts any value; its type is fixed per construction site (a
record type with such open fields behaves as an inferred-generic type — each
use site gets its own instantiation).

Records and arrays have **reference semantics**: mutating through one binding
is visible through every binding that shares the object. `const` makes a
binding immutable (and forbids mutating through it).

### Structural subtyping

A value of a record type is usable wherever a _structurally smaller_ record is
required: a function parameter constrains a value only by the members it
actually uses (unannotated parameters), or by the named type's members
(annotated). A record with more fields satisfies a requirement of fewer
fields. Arrays are invariant in their element type. Sum types are nominal —
only the declared type matches.

When an **anonymous record** (`{ field: value, ... }`) is passed to an
unannotated parameter, the compiler derives the parameter's required "row" of
fields from the callee body (interprocedurally), checks the argument against
it at the argument's own span, and compiles a view of the value for that
parameter.

### Anonymous-record method dispatch

Calling a method on a structural value resolves it against the **in-scope**
record types — those declared in or imported into the calling module
(builtins and the implicit prelude count): if **exactly one** such type
declares that method and the value satisfies that type's fields, the call
dispatches to it with no annotation. An anonymous value never adopts a type
the module has not imported, even when its shape matches; the error names the
satisfied type and the missing import. Zero candidates produce a near-miss
diagnostic; several candidates make the call ambiguous — a compile error at
the value asking for an annotation.

This scoping gates only the adoption of a type by an anonymous value. A value
whose nominal type is already known — the return of an imported function,
say — dispatches its methods by that type; the type's name need not be
imported.

### Structural conversion

For a record type `T`, `T.from(v)` yields `T?`: the record value when `v`
structurally has all of `T`'s fields (decided for the actual value at that
call site), else `null`. Pair it with `if let`:

```
if let person = Person.from(obj) {
    ...
}
```

## Interfaces

`type B: A = ...` requires `B` to provide every member of `A`, checked at
compile time; multiple constraints are comma-separated (`type B: A, C`). No
implementation is inherited — the constraint is pure satisfaction:

- a required **field** must exist with an _invariant_ type (fields are
  mutable, so a subtype field would be unsound);
- a required **method signature** must be implemented with invariant
  parameters and covariant return;
- for a sum type, **every variant** must satisfy the interface;
- conflicting field requirements from multiple constraints are reported at the
  type.

## Methods

Methods are implemented outside the type with `fun T.m(...)`, **in the same
module that declares `T`**. A method whose first parameter is `self` is an
instance method (called `value.m(...)`); one without is a static method
(called `Type.m(...)`). `Self` in the body names the type. A method is in
scope wherever the type is, with no separate import.

There is **no UFCS**: a free function is never callable as `recv.f(...)`, and
a method is never callable as `f(recv, ...)`. The standard library defines
methods on primitive and array types with the receivers `fun string.m`,
`fun string[].m`, and `fun infer[].m`; user code cannot add methods to types
it does not declare.

Method return types are inferred like function return types. A method call on
a value whose concrete type is not yet known is resolved when it becomes
known — per instantiation.

## Nullable

`T?` is a nullable type. `null` is its own value; `T` promotes into `T?`
freely.

An un-narrowed nullable allows only: the boolean test positions below,
`x == null` / `x != null`, and `!x`. Field access, indexing, arithmetic, or
passing it where `T` is required are compile errors
("nullable value must be checked for null before use").

**Narrowing** — inside these forms, the value has type `T`:

- `if x { ... }` and `if x != null { ... }` — in the truthy branch;
- `if !x { return ... }` / `if x == null { return ... }` — after the guard,
  when the guard block always returns;
- `if let y = x { ... }` — `y` is the non-null value in the then branch.

A narrowed module global — or a local that a closure assigns — is re-widened
after any call, since the call could reassign it.

### Absent fields in conditions

Inside a conditional, accessing a field the record does not have yields `null`
(type `never?`) instead of a compile error, and the branch folds to its
negative arm. This is what lets structurally typed code probe optional
fields (`if person.name { ... }`). Outside a condition, a missing field is
still an error, and a missing field on a _sum type_ value is an error even in
a condition.

## Result

`T!` is the built-in `Result` type with variants `Ok { value: T }` and
`Err { error: E }`; the error payload type `E` is inferred from the `error(x)`
calls the function makes (all error sites of one function must reconcile to
one payload type).

- `error(x)` constructs an `Err`. It is a reserved builtin.
- A function is _fallible_ when its body uses `error(...)` or `expr!`, or its
  declared return type is a Result. In a fallible function, `return v` with a
  plain value wraps it as `Ok { value: v }` automatically; returning a Result
  value passes it through whole.
- The postfix **`!`** operator propagates: `expr!` unwraps an `Ok` or returns
  the `Err` early from the enclosing function. It is allowed only inside a
  function or closure whose return can be fallible — not at the top level and
  not in a function explicitly annotated with a non-Result return type.
- Consume a Result by matching `Ok { value }` / `Err { error }`.
- A function that can only ever `error(...)` (no successful return) cannot be
  used where a value is required.

Separately, returns of `null` and returns of `T` in one function join to
`T?`.

## Polymorphism and inference

- **Let-polymorphism**: `let id = (x) -> x` may be used at several types; each
  use instantiates the inferred scheme freshly.
- **Function polymorphism**: an unannotated function is re-checked per call
  site with the concrete argument types, then compiled per instantiation. This
  is stronger than a single inferred scheme — `fun add1(x) { return x + 1 }`
  works for `int32`, `int64`, and `float64` callers alike.
- **`infer`** in a signature marks an inference hole explicitly; each
  occurrence is independent.
- **Generic records** need no type parameters: leave fields unannotated (or
  build containers empty) and each construction site fixes its own
  instantiation. Methods share the record's inferred parameters, so a
  container's `set`/`get` agree on the element type without a witness value.
- **`fun T.m(self) -> infer!`** declares a reflective template whose result
  type is fixed by each call site's expected type — see
  [Compile-time reflection](/references/reflection/#generic-decoders-with---infer).
- When a concrete type is only known at runtime (e.g. decoding external
  data), the needed specialization is compiled at that moment; this is
  invisible to the type rules.

There is **no explicit type-parameter syntax** (`<T>` does not exist).

### Type slots and refinements

A record can name its type parameters as **slots** — fields declared with the
`type` keyword as their type — and refer to them elsewhere with `Self.slot`. A
slot has no runtime storage: it never appears in the layout, in `fields()`, or
in a construction literal. It only names a type another field is expressed
over.

```prepoly
type _Entry = {
    key
    value
}

type Map = {
    key: type            // type slots: the key/value types, no storage
    value: type
    entries: _Entry { key: Self.key, value: Self.value }?[]
    count: int64
}
```

`Base { field: T, ... }` is a **refinement**: it pins the named slots (and
fields) of a record, yielding a concrete instance. Written as the right-hand
side of an alias declaration it gives that instance a name:

```prepoly norun
type StringInts = Map { key: string, value: int64 }
```

- An omitted slot stays open (inferred), so a partly-refined alias is still
  generic in the slots it does not mention.
- A slot may be pinned to anything; a real field that already has a concrete
  type may only be refined to that same type (a mismatch is rejected).
- The alias is not a new nominal — it unifies with any matching instance, so a
  witness-free value built by the container's constructor is accepted where the
  refined type is annotated.
- Annotating a binding with the alias pins the container's types up front, so
  `let m: Counts = HashMap.new()` (with `type Counts = HashMap { key: string,
  value: int64 }`) is a usable `string -> int64` map: subsequent stores are
  checked against the pinned value type, so a bare integer literal or an int32
  value stores as int64.

Field types are resolved like Hindley–Milner inference: each field and slot is
assigned a type variable and `Self.field` resolves to it. A field whose type
refers back to itself through the `Self.field` chain (`a: Self.b`,
`b: Self.a`) is a circular unification and is **rejected** by the occurs-check.

## Match exhaustiveness

A `match` whose scrutinee is a sum type must either name every variant or
contain a catch-all arm (`_` or a whole-value binding). A variant arm counts
as covering its variant only when all of its field sub-patterns are
irrefutable (a literal field pattern makes the arm partial). Matches over
non-sum values (integers, strings) are not exhaustiveness-checked; add a `_`
arm. A function with a declared non-void return type must return a value on
every path (`while true` without `break` counts as diverging).

## Definite assignment

An annotated `let` may omit its initializer (`let p: Point`). The binding must
then be definitely assigned before use:

- assigning the whole binding completes it;
- for a record type whose field skeleton is default-constructible (numbers,
  bool, string, nullable, arrays, tuples, and records of those — not sums or
  functions), assigning **every field individually** also completes it;
- branches join by intersection (both arms must assign); paths that return or
  diverge drop out;
- a `for field in fields(x)` loop that assigns `x[field]` on every non-exiting
  path counts as assigning all fields (see [Reflection](/references/reflection/));
- reading the binding — or capturing it in a closure — before completion is a
  compile error. `typeof(x)` and `fields(x)` only read the type and are
  allowed.

## Recursion and program order

- Self-recursion needs no annotations: a recursive call is typed against the
  function's declared or previously inferred return type.
- **Mutual recursion** should carry return-type annotations on the functions
  in the cycle; each recursive call then types against the annotation. Without
  them the checker may be permissive, but the back end can reject the cycle
  when it cannot fix a concrete return type.
- Functions and types may be used textually before their definitions. A
  module-level **binding** may not: globals initialize in order, and reading
  one before its initializer has run is a compile error.

## Closures

Closures **capture by reference**: the closure sees (and may mutate) the live
binding, and mutations through the closure are visible outside. A closure's
parameter and return types are inferred (annotations optional); a closure used
polymorphically instantiates per call. A closure parameter shadows a global
function of the same name — the local value is called. Each closure has its
own return context, so `!` inside a closure propagates to the closure's own
return value.

## Concurrency typing

`spawn(f)` requires a zero-parameter closure and returns `void`; `with(c, f)`
requires a one-parameter closure and returns the closure's result; `sync()`
takes nothing. Ownership analysis of captured values happens after type
checking — see the [concurrency reference](/references/concurrency/).
