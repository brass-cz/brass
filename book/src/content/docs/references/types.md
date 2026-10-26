---
title: "Type system"
description: "The type system in full: literals, conversions, parameter passing, structural typing, nullable, Result, and inference."
---

Brass is statically typed with flexible type inference. Every function body
is checked before it can execute; `brass check` produces the complete
whole-program verdict. Annotations constrain types, but are never required
for safety. See [Execution model](/references/execution/) for when the default
run performs each check.

The inference is Hindley-Milner-**style**, unification over type variables,
but deliberately not textbook HM; it deviates where a scripting language
benefits:

- A polymorphic function is not generalized once into a principal type
  scheme; it is checked again at each call site with the actual argument
  types and compiled per concrete instantiation (monomorphization). This is
  what lets most code omit annotations without losing precision.
- Structural typing feeds inference: an unannotated parameter is constrained
  by the members the body actually uses, not by a nominal signature.
- Numeric literals default by magnitude and _adapt_ to the context they flow
  into, and value-preserving numeric conversions are inserted implicitly at
  flow points (see [Literals](#literals) and
  [conversions](#explicit-conversions)). Textbook HM would reject these
  mixed-type uses instead of converting.

## Primitive types

| Kind              | Types                              |
| ----------------- | ---------------------------------- |
| Signed integers   | `int8` `int16` `int32` `int64`     |
| Unsigned integers | `uint8` `uint16` `uint32` `uint64` |
| Floats            | `float32` `float64`                |
| Other             | `bool` `string` `void`             |

`void` is the no-value return type. A call that returns `void` produces no
value to name: it cannot be bound with `let`/`const` (`let _ = f()` discards
it) or passed as an argument. There is no character type: a character
is a one-character `string`. Diagnostics and `typeof` may additionally
mention `never` (the type of `null` before it meets a context, spelled
`never?`); it is not writable in source.

## Literals

- The default type of an integer literal is `int32` when the value fits,
  otherwise `int64`, otherwise `uint64` (so `9223372036854775807` is an
  `int64` and `18446744073709551615` a `uint64`). A larger value is a compile
  error.
- A minus sign written directly before an integer literal belongs to the
  literal: `-1` is one literal whose value is minus one, and that value (sign
  included) decides its type, so `-2147483648` is an `int32` and
  `-9223372036854775808` an `int64`. A value below `INT64_MIN` is a compile
  error.
- The default type of a float literal is `float64`.
- A literal _adapts_ to an annotated type when it fits: `let b: int8 = -128`
  is fine, `let b: int8 = 300` is a compile error (never a silent wrap). A
  float literal adapts to either float width if its value remains finite at
  that width; rounding (for example, `0.1`) and underflow to zero are allowed.
  Overflow is an error, including `1e39` in a `float32` context and `1e400`
  at the default `float64` width. An integer literal in a float context
  becomes that float when the float represents its value exactly:
  `let e: float32 = 3` is `3.0`, while `16777217` does not fit `float32`
  (24 mantissa bits) and is a compile error.
- The required type can also come from a container the value flows into: a
  bare integer literal passed to a method of a map whose value type is pinned
  to `int64` (by a first store or a refinement annotation) is checked against
  `int64`, so it types as `int64` rather than defaulting to `int32` (and an
  `int32` value widens at the call).

### Bracket literals

A bracket literal `[...]` is typed in this order:

1. A type annotation (or another inference result, such as the parameter it is
   passed to, or the declared return a `return` flows into) decides: the
   literal takes that type, also under a nullable (`[int32, int32]?`) or
   fallible (`-> [string, string]!`) requirement, and each element flows into
   its position's type.
2. Elements that are all numbers share their value join, as the branches of
   an `if` join (see [Flow conversions](#flow-conversions)): `[big, 1]` with
   `big: int64` and `[an_int32, an_int64]` are `int64` sequences, `[1, 2.5]`
   is a `float64` sequence. This holds in a generic function or closure body
   at each instantiation: with `const pair = (a, b) -> [a, b]`, `pair(1, 2)`
   is an `int32[]`. Otherwise elements that cannot unify make it a
   **tuple** (as do numbers with no common type, such as `int64` and
   `uint64`), but a `null` element never does: `null` unifies with any
   element type, so `[4, null, 65]` is a sequence of `int32?`.
3. Bound immutably (`const`), it is a **fixed-length array**:
   `const a = [1, 2, 3]` is `int32[3]`.
4. Bound mutably (`let`) or in any other position, it is a **growable array**:
   `let a = [1, 2, 3]` is `int32[]`.

A fixed-length array is usable where a growable array of the same element is
required (the length is extra static information), but not the reverse.
`[lo..hi]` builds the half-open integer range as an array. Its element type,
which a `for` loop over it also counts in, is the type the operator rule
(see [In operators](#in-operators)) gives `lo` and `hi`: `[0..a.len()]` is
`int64[]`, and `[b..256]` with `b: uint8` is `int32[]`, so the count reaches
`hi`.

## Numeric conversions

### In operators

An arithmetic, comparison, bitwise or shift operator between two numeric
operands converts both to one **operand type** and computes there:

- A literal operand (a negated one like `-1` included) _adapts_ to the other
  operand's type when it fits that type: an integer literal fits an integer
  type whose range holds its value or a float type that represents it
  exactly; a float literal fits a float type at which it stays finite
  (rounding is allowed, as for any float literal). With `b: uint8`, `b + 1`,
  `b & 15` and `b >> 4` are `uint8`; with `f: float32`, `f * 2` and
  `f * 0.5` are `float32`.
- Otherwise both operands convert to their **common type**: the smallest type
  both convert to value-preservingly. So `int32 + int64` is `int64`,
  `b + 300` is `int32` (300 does not fit `uint8`), and `int32 + float64` is
  `float64`. Two literals meet at their default types' common type. Pairs
  with no value-preserving common type (`int64` with `uint64`, `int64` with
  `float64`, a `uint64` with a negative literal) are a compile error; convert
  one side explicitly.

The operation is computed at the operand type, and integer arithmetic wraps
at that width (see
[runtime behavior](/references/execution/#runtime-behavior-guarantees)):
`b + 100` with `b = 200` is the `uint8` value `44`. A comparison yields
`bool`; every other operator yields the operand type. `%`, the bitwise
operators and the shifts take integers only. `+` on two strings concatenates.

A compound assignment `x op= e` is typed exactly as `x = x op e`: the rule
above types `x op e`, and the result then flows into `x` like any assignment
(see below). So `u += 1` keeps `u`'s type for every integer kind, while
`u += 300` on a `uint8` is a compile error (the `int32` sum would narrow).

Operators compute at their operands' settled types. A conversion applied to
an already typed result does not change how the operation computes.

### Flow conversions

Numeric values also convert automatically when they _flow_ into a numeric
position of another type, but only when the conversion is
**value-preserving**. The flow positions are an assignment, an argument
(including one to a container method such as `push`, `insert` or `set`), a
return value, a compound assignment, an element/field store, an element of an
array or tuple literal under an expected type, and a branch of an
`if`/`match` that yields a value. The conversions are:

- an integer into a strictly wider integer of the same signedness;
- an unsigned integer into a strictly wider signed integer;
- `float32` into `float64`;
- an integer into a float whose mantissa holds every value exactly: up to
  `int32`/`uint32` for `float64`, up to `int16`/`uint16` for `float32`.

So `let b: int64 = an_int32`, `total += an_int32` (with `total: int64`) and
`ys.push(an_int32)` (with `ys: int64[]`) all widen the value. Anything lossy
(a narrower integer, a sign change, a narrower float, `int64` into `float64`,
or float into int) never happens implicitly; the error suggests the explicit
conversion.

The value of an `if`/`match` with numeric branches is the join of its
branch values, by the rule a function's returns join by (see
[Inferred return types](#inferred-return-types)): numbers meet at the
smallest type they all convert to, and a branch written as a literal adapts
to the other branches when it fits, exactly as a literal operand does. So
`if c { x } else { 0 }` with `x: int64` is an `int64`, and
`if c { b } else { 300 }` with `b: uint8` is an `int32`. When the value flows
into a numeric position (an annotated binding, a parameter, a return, a
field), the branches written as literals first adapt to that position's type
if every one of them fits it, as a literal flowing there directly would:
`let small: uint8 = if c { 200 } else { 7 }` is a `uint8`. The other branches
keep their types, and the joined value then flows into the position by the
rules above (`if c { an_int32 } else { 7 }` into a `uint8` is still an error).
An `if` or `match` in statement position has no value: its arms' trailing
values are discarded and never joined (see
[Expressions](/references/syntax/#expressions)).

A `T` value also flows freely into a `T?` position. A nullable value never
flows into a non-nullable one; it must be narrowed first.

### Numerically open bindings

An unannotated `let` or `const` initialized by a numeric literal, or by
arithmetic using only literal-origin operands, is numerically open. Its type
is the smallest value-preserving join of the initializer's default type,
every numeric value assigned to it, and demands propagated through its
literal origin. The default is a floor: `int32`, otherwise `int64`, otherwise
`uint64` by integer magnitude, and `float64` for a float literal. Assignment
to a `const` remains an error.

| Binding and later assignment | Settled type |
| --- | --- |
| `let x = 0` followed by `x = an_int8` | `int32` |
| `let total = 0` followed by `total = total + an_int64` | `int64` |
| `let x = 0` followed by `x = 1.5` | `float64` |
| `let x = 0` followed by `x = a_uint64` | Error: `int32` and `uint64` have no value-preserving join |

Copies, literal-only arithmetic, and unannotated forwarding returns preserve
origin. A demand through `let acc = init` therefore settles both `acc` and
`init`. Unannotated parameters supplied literal-origin arguments negotiate in
the same way: an `int64[]` folded with `fold(0, (s, x) -> s + x)` has an
`int64` initializer, accumulator, and result. A binding's literal initializer
sets its minimum type; arguments joined at a closure's applications adapt to
each other under the closure parameter rule.

Annotations, explicit conversions, already typed values, and field or
container reads end origin propagation. All reads of an open binding use its
settled type, including reads before the assignment that widens it; each use
must accept that type. Only top-level statements settle a module-level
binding. Function-body writes must fit that settled global type.

A statically discarded arm contributes nothing in that instance. When a type
fold depends on an open binding, inference starts at its floor, evaluates the
folds, and grows from the live contributions until the type and folds agree.
A contradiction or failure to reach a self-consistent solution requires an
annotation.

### Explicit conversions

| Conversion                        | Result    | Notes                                                                           |
| --------------------------------- | --------- | ------------------------------------------------------------------------------- |
| `intN.from(x)`                    | `intN!`   | range-checked; `Err` when out of range                                          |
| `intN.parse(s)`                   | `intN!`   | parses a string                                                                 |
| `floatN.from(x)`                  | `floatN`  | **total**: always succeeds, precision loss is accepted because it was asked for |
| `floatN.parse(s)`                 | `floatN!` | parses a string                                                                 |
| `string.from(x)`                  | `string`  | total; renders any value exactly as `"{x}"` and `print` do (see below)          |
| `T.from(v)` for a record type `T` | `T?`      | structural conversion: see [below](#structural-conversion)                      |

`int32.from(3.9)` can fail (and truncates toward zero on success), so it
returns a Result; `float64.from(big_int64)` cannot fail, so it returns a plain
float even though it may round. Converting a `uint64` uses the whole unsigned
range, including values above `INT64_MAX`. The prelude also provides free
function aliases (`int32_from`, `int32_parse`, `float64_from`,
`float64_parse`, `string_from`).

Every value has a text rendering except a `void` (the result of a call that
returns nothing) and a function value. Rendering one -- `print`/`println`, a
`"{v}"` segment, `string.from`, the built-in `debug` -- is a compile-time
error, also when it sits inside a nullable, an array or a tuple. A record or
variant field holding a function value renders as `<opaque>`.

## Equality

`==` and `!=` compare two numbers (converted to their common type first) or two
values of the **same** type, structurally:

- integers and bools by value; floats by IEEE equality (`NaN != NaN`,
  `0.0 == -0.0`); strings byte for byte;
- records field by field;
- sum values by variant, then the variant's payload fields;
- arrays by length, then element by element; tuples element by element;
- a nullable field or element is equal when both sides are `null`, unequal
  when only one is, and otherwise compares the present values;
- function values by identity: a closure equals only itself. Each use of a
  let-polymorphic closure binding (see
  [Polymorphism](#polymorphism-and-inference)) builds its own closure value,
  so such a binding is not equal to itself; a closure whose parameters are
  all annotated is one value.

A nullable _operand_ only compares against `null` (`x == null`); narrow it to
compare its value. `HashMap` keys use this same equality.

## Parameter passing

How an argument is passed is part of the signature, and it is inferred when
not annotated:

| Annotation                | Passing                               | Callee mutation                                            |
| ------------------------- | ------------------------------------- | ---------------------------------------------------------- |
| _(none, body only reads)_ | shared reference                      | rejected by inference (would reclassify)                   |
| _(none, body mutates)_    | **private deep copy** at callee entry | stays local, invisible to the caller                       |
| `ref(T)`                  | immutable reference                   | rejected                                                   |
| `ref(mut(T))`             | mutable reference                     | **writes through** to the caller                           |
| `mut(T)`                  | mutable deep copy                     | stays local                                                |
| `infer`                   | read-only deep copy                   | rejected; mutating an `infer` parameter is a compile error |
| _(numeric type)_          | by value                              | n/a; numbers are copied                                    |

`ref(T)`, `ref(mut(T))`, and `mut(T)` are allowed only as a whole
parameter annotation: on functions, methods, closures, method signatures in
type bodies, and parameter positions of function types such as
`(ref(mut(T))) -> void`. Here `T` contains no `ref` or `mut` annotation.
They are not value types: return types, variable/constant annotations, fields,
type arguments, and array/nullable/fallible wrappers cannot contain them.
For example, `ref(T[])` is a parameter annotation, but `ref(T)[]` is invalid.
Other nesting, including `ref(ref(T))` and `mut(ref(T))`, is invalid.

Details:

- "Mutates" means a field or element store, a mutating method (`push`,
  `insert`, `remove`, `pop`), a loop-variable write-back, or passing the value
  on into a position known to mutate. Rebinding the parameter name (`p = ...`)
  is not a mutation of the caller's value.
- Passing the value to a function value counts as mutating it when that value
  may take it by `ref(mut(T))`: a closure bound to a local whose parameter is
  annotated so, a parameter annotated with such a function type, or an
  unannotated function-valued parameter (its passing modes come from each
  call site, so it is assumed to write through). In
  `fun call(f, b) { f(b) }`, `b` is therefore a private copy: a `ref(mut)`
  closure passed as `f` changes `call`'s copy, never the caller's value.
- The deep copy happens at **callee entry**, once, driven by the parameter's
  type.
- The table applies to closure parameters exactly as to function
  parameters: a closure that mutates an unannotated parameter works on its
  own copy, and only a `ref(mut(T))` closure parameter writes through (so a
  `const` value cannot be passed to it). The one exception is the closure
  literal of a `with(c, f)` call, whose parameter is the guarded shared
  object itself (see [Concurrency](/references/concurrency/)).
- `ref(mut(T))` also requires the _argument_ to be mutable (`let`, not
  `const`), even if the body does not currently mutate it. A value only
  readable where it is passed -- a `const`, or an immutable `ref(T)`
  parameter -- is rejected there, and so when handed to a function value
  whose parameter is `ref(mut(T))`: in `fun apply(f, v: ref(P)) { f(v) }`,
  each call is judged by the function value it passes as `f`.
- `infer` may be combined structurally: `infer[]` requires "an array, element
  type inferred"; `infer?[]` an array of nullables. Each occurrence of `infer`
  is an independent inference hole.

### `self`

`self` is permitted only as the first parameter of a method implementation or
a method signature in a type body. It cannot be a free-function or closure
parameter. The `self` receiver is a special case: unannotated `self` is always a
_reference_. A method that only reads `self` receives `ref(Self)`; one that
mutates it receives `ref(mut(Self))`, so the change is visible to the caller.
Annotate `self: Self` to work on an owned deep copy instead (mutations stay
local).

### Optional trailing parameters

A trailing parameter of nullable type may be omitted at a free, static, or
instance call; it defaults to `null`. Several trailing nullable parameters may
be omitted together, followed by an implicit trailing `Location` when the
signature declares one. The prelude's `assert(cond, msg: string?)` is callable
as `assert(cond)`.

A function named as a value has the arity its use needs, anywhere from its
required parameters to all of them: with `fun greet(name: string, title:
string?)`, `["x", "y"].map(greet)` applies a one-parameter function (the
omitted `title` is `null`), while a use expecting `(string, string?) ->
string` passes both. Its first application or expected function type fixes
that arity.

## Records and structural typing

`type Name = { fields... }` declares a nominal record type. A field without a
type annotation accepts any value; its type is fixed per construction site (a
record type with such open fields behaves as an inferred-generic type: each
use site gets its own instantiation).

Records and arrays have **reference semantics**: mutating through one binding
is visible through every binding that shares the object. `const` makes a
binding immutable (and forbids mutating through it).

When constructing a sum variant, each payload value flows through its declared
field type, including the same numeric widening and nullable promotion used by
record fields and function arguments.

### Structural subtyping

A record value satisfies a _structurally smaller_ record requirement only
where the receiving code is compiled for the value's own type: a
**function or method parameter**, annotated or not. An unannotated parameter
requires the members the body uses; an annotated one requires the named
type's members, each field at its declared type. A record with more fields
satisfies a requirement of fewer fields, never the reverse. The callee is
instantiated at the argument's type, so `describe(dog)` with
`fun describe(a: Animal)` runs the body with `a` a `Dog` (with `a: Animal?`,
a `Dog?`), and a primitive passed for a protocol record such as `Display`
runs it at that primitive. The body is checked at that type too.

Arrays are invariant in their element type, at a parameter as well. Sum types
are nominal: only the declared type matches, unless the sum **declares a
parent** (`type Child: Parent`), which admits it at the parent's flow sites
by rebuild. See
[Declared sum subtyping](/references/syntax-sugar/#declared-sum-subtyping).

Every other flow site **stores** the value in a slot that keeps its declared
type. Records have reference semantics and a store converts nothing, so the
value must name the same record and sum declarations as the slot, at every
depth. The storage sites are:

- an annotated `let`/`const`, an assignment, an annotated `return`;
- a record field (initializer or store) and a sum variant payload;
- an array or tuple element: a literal's elements under an expected type,
  `push`/`insert`, an index store;
- a container slot the receiver pins: a map key or value passed to `set`;
- the parameters and result of a function-typed value: a closure or a
  function value is compiled once, for its own signature, so
  `(Animal) -> string` is not usable as `(Dog) -> string` (nor the reverse),
  and neither is `() -> Child` as `() -> Parent` for a declared sum subtype.

```brass
type Animal = { name: string }
type Dog = { age: int32, name: string }

fun describe(a: Animal) -> string {
    return a.name
}

let dog = Dog { age: 3, name: "Rex" }
println(describe(dog))          // a parameter: the body runs at `Dog`
// let a: Animal = dog          // error: cannot store a `Dog` in a slot of type `Animal`
if let a = Animal.from(dog) {   // explicit: a new `Animal` with `dog`'s fields
    println(a.name)
}
```

The same holds inside a callee instantiated at a wider argument:
`fun keep(a: Animal) -> Animal { return a }` called with a `Dog` would return
a `Dog` into an `Animal` result and is rejected for that call.

A store still performs the conversions defined for flows: numeric widening,
`T` into `T?`, and the rebuild of a declared sum subtype as its parent (also
into a nullable parent, `Shape?`). The rebuild applies to the stored value
itself only; a `Child[]` is not a `Parent[]`, nor a `Child!` a `Parent!`.

An **anonymous record literal** whose fields are exactly a declared record
type's is built _as that record_ where it flows into that type, in a slot or
at a parameter annotated with it: `let p: Point = { x: 1, y: 2 }` constructs
a `Point`. This also holds for a literal that is a branch value of an `if`,
`match` or block whose value flows there
(`let p: Point = if c { { x: 1, y: 2 } } else { origin }`, or a parenthesized
arm `1 => ({ x: 1, y: 2 })`): a requirement that shapes a construction (a
record, array, tuple or function type) reaches every branch value, as it
reaches a direct initializer. In a slot, a literal with an extra or a missing
field is an error, and an anonymous record held in a variable is not
converted (use `T.from(v)`). A protocol-like record type, one whose members
are methods such as `Display`, is accordingly a parameter annotation:
`fun show(v: Display)` takes any value with a `display` method, while
`let d: Display = 42` is an error.

When an **anonymous record** (`{ field: value, ... }`) is passed to an
unannotated parameter, the compiler derives the parameter's required "row" of
fields from the callee body (interprocedurally), checks the argument against
it at the argument's own span, and compiles a view of the value for that
parameter. The view holds the fields the body uses, each at the argument's
own type, so the callee computes exactly as it would on a record with those
fields (a use that needs another type, such as an `int64` parameter, only
checks that the field flows into it). A field the body uses only behind a
presence test (`if p.f`, `if let v = p.f`) may be absent, or of a type that
use cannot take; the view then holds `null` there and the body takes its
fallback path. Rendering the whole parameter shows the view's fields.

### Anonymous-record method dispatch

Calling a method on a structural value resolves it against the **in-scope**
record types: those declared in or imported into the calling module (builtins
and the implicit prelude count). If **exactly one** such type declares that
method and the value satisfies that type's fields, the call dispatches to it
with no annotation. An anonymous value never adopts a type the module has not
imported, even when its shape matches; the error names the satisfied type and
the missing import. Zero candidates produce a near-miss diagnostic; several
candidates make the call ambiguous: a compile error at the value asking for an
annotation.

This scoping gates only the adoption of a type by an anonymous value. A value
whose nominal type is already known (the return of an imported function, say)
dispatches its methods by that type; the type's name need not be imported.

### Structural conversion

For a record type `T` that declares no static `from` of its own, `T.from(v)`
yields `T?`: the record value when `v` structurally has all of `T`'s fields
(decided for the actual value at that call site), else `null`. Each field's
value must flow into `T`'s field type by the
[flow conversions](#flow-conversions): the same type, a value-preserving
numeric widening (an `int32` field fills an `int64` or `float64` one), or a
value (or `null`) filling a nullable field. A field that would need a lossy
conversion makes the result `null`. When `v` is written as an anonymous record
literal, a field given as a numeric literal adapts to `T`'s field type when its
value fits, as a literal does in any flow: `G.from({ x: 5 })` with
`x: float32` builds `G { x: 5.0 }`. A type's own declared static
`fun T.from(..)` (without `self`) shadows this builtin conversion: `T.from(v)`
then calls that method with its own parameters and return type. An instance
method `fun T.from(self, ..)` leaves structural conversion available.

Pair the builtin conversion with `if let`:

```
if let person = Person.from(obj) {
    ...
}
```

`v` may be of **any** type: a value that is not a record at all simply has
none of `T`'s fields, so the conversion answers `null` rather than failing to
compile. This lets one function take a value whose type differs per call site
and branch on what it turned out to be:

```
fun as_text(value) -> string! {
    if let p = Path.from(value) {     // a Path: render it
        return p.to_string()
    }
    if value.chars {                  // a string: it is already text
        return value
    }
    return error("expected a string or a `Path`")
}
```

The second guard is a **member-presence test**: an uncalled member is a
compile-time question about the argument's type, and the arm behind a member
that type does not have is statically dead: never checked, never emitted (see
[Absent fields](#absent-fields)). The `if let` over `Path.from`, by contrast,
is an ordinary nullable test whose paths are both checked, which is why the
string case needs a guard of its own: without it, `return value` would be
checked against the `string` return with `value` still a `Path`. The same
guard is written more directly as `value.is_string`, since each primitive
type implements only its own `is_<type>` method, so the presence test
doubles as a type test (see
[the reflection reference](/references/reflection/#member-presence-xm-without-a-call)).

## Type tests

`if value: Type { ... } else ...` tests the **static type** of `value`. The
test is decided entirely at compile time, per monomorphic instance of the
enclosing function: the subject's concrete type either satisfies the tested
type or it does not, the selected arm alone is type-checked and compiled, and
the unselected arm is pruned exactly like the dead arm of a
[member-presence test](#absent-fields). Nothing is tested at
run time, and `else if` chains dispatch on the first satisfied test.

The subject is one postfix-level expression: an identifier, literal, `self`,
field access, call, index, postfix `!`, or a parenthesized expression.
A binary or prefix subject must be grouped: `(a == b): bool` and `(-x): int32`.
`if !v: T` is invalid; to negate the test, write `if !(v: T)` with the
parentheses. These are the only two test forms: a parenthesized test cannot
be used as a value, inside `&&`/`||`, or as `if (v: T)`.

`if !(v: T) { A } else { B }` has the same behavior as
`if v: T { B } else { A }`, including compile-time pruning, expression
results, return types, and fallibility. Without `else`, the body runs only
when the type test fails. For a negated test, `infer` holes are pinned by
the `else` arm, where the positive test holds; with no `else` they remain
unconstrained. Negated tests can also head an `else if`.

A type satisfies the test when it is:

- **the tested type itself** (representation-exact: `int32` does not satisfy
  an `int64` test and `T` does not satisfy a `T?` test -- matching never
  converts), or
- **a subtype of it**: a record that
  [structurally satisfies](#structural-subtyping) the tested type's fields
  and methods (`anonymous { ... }` and interface-style record types both
  work), or a sum that [declares the tested sum as a
  parent](/references/syntax-sugar/#declared-sum-subtyping). A `T[]` test
  also accepts a fixed-length `T[n]`.

Inside the selected arm the subject keeps its **own** type -- the test never
reinterprets or rebuilds the value. (Passing the subject onward from the arm
goes through the ordinary flow rules, views and rebuilds included.)

`infer` in the tested type is a hole:

- A hole constrained by the matching arm's use of the subject takes that type:
  in `if v: infer { to_bytes(v) }` the hole reads as `string`, because that
  is what `to_bytes` accepts. The pinned type must come out the same for
  every instantiation of the enclosing function -- a test whose holes resolve
  differently per call site is a compile error asking for an annotation.
- A hole nothing constrains matches any type: `infer` alone matches
  everything, `infer[]` matches any array.

Consequences of the per-instance decision:

- Inside a generic (unannotated) function, nothing is decided at the
  definition; each call site's instantiation selects and checks its own arm.
  An arm no instantiation selects is never fully checked, like any other
  statically dead code.
- A path this instance never passes contributes NOTHING: neither the
  unselected arms nor the statements a selected always-returning arm makes
  unreachable. Their `return`s do not join the instance's return type -- one
  arm may return `int32` and another `string`, each instance keeping its own
  -- and an `error(...)` on such a path does not make the instance fallible.
- Fallibility is therefore per instance too: only an instance whose live path
  reaches an `error(...)`/`!` returns a `Result`. An instance whose live path
  ONLY errors behaves like any function that only returns errors: its Ok
  payload is uninhabited, and reading it concretely is rejected.

```
fun length(val) {
    const bytes = if val: infer {         // string (to_bytes pins the hole)
        to_bytes(val)
    } else if val: uint8[] {              // exact match, beats infer[]
        val
    } else if val: infer[] {              // any other array
        val
    } else {
        return error("unsupported")
    }
    return bytes.len()
}
```

`length("hi")` compiles the first arm only and returns a bare `int64`;
`length(to_bytes("hi"))` the second, `length([1, 2, 3])` the third -- both
also bare. Only `length(true)` selects the `else` and returns a `Result`
(always its `Err`).

## Interfaces

`type B: A = ...` requires `B` to provide every member of `A`, checked at
compile time; multiple constraints are comma-separated (`type B: A, C`). When
`A` is itself a **sum** type, the declaration means
[declared sum subtyping](/references/syntax-sugar/#declared-sum-subtyping)
instead: exact variant coverage, widening-only variants, and admission at the
parent's flow sites by rebuild. For record constraints, no implementation is
inherited; the constraint is pure satisfaction:

- a required **field** must exist with an _invariant_ type (fields are
  mutable, so a subtype field would be unsound);
- a required **method signature** compares the full signature: parameter
  types and passing modes must match exactly (parameters are invariant), and
  the return type may be a structural subtype of the required one (a record
  with more fields) but otherwise matches exactly, with no numeric or
  nullable conversion;
- for a sum type, **every variant** must satisfy the interface;
- conflicting field requirements from multiple constraints are reported at the
  type.

## Methods

A method's name must differ from every field name of its record, or every
field name across all variants of its sum. This applies to method signatures
in type bodies and implementations written as `fun T.m(...)`.

Methods are implemented outside the type with `fun T.m(...)`, **in the same
module that declares `T`**. A method whose first parameter is `self` is an
instance method (called `value.m(...)`); one without is a static method
(called `Type.m(...)`). `Self` in the method's signature and body names the
type, exactly as writing its name does (`fun B.make(x: int32) -> Self`). A
method is in scope wherever the type is, with no separate import. A unit
variant is a value, so `Sum.Variant.m(...)` calls the instance method `m` on
that variant (`List.Nil.size()`); a static method may also be reached
through a variant qualifier (`Sum.Variant.make()` calls `Sum`'s static
`make`).

There is **no UFCS**: a free function is never callable as `recv.f(...)`, and
a method is never callable as `f(recv, ...)`. The standard library defines
methods on primitive and array types with the receivers `fun string.m`,
`fun string[].m`, and `fun infer[].m`; user code cannot add methods to types
it does not declare.

Method return types are inferred like function return types. A method call on
a value whose concrete type is not yet known is resolved when it becomes
known, per instantiation.

## Nullable

`T?` is a nullable type. `null` is its own value; `T` promotes into `T?`
freely. Nullability does not nest: `T??` is the same type as `T?`.

An un-narrowed nullable allows only: the boolean test positions below,
`x == null` / `x != null`, and `!x`. Field access, indexing, arithmetic, or
passing it where `T` is required are compile errors
("nullable value must be checked for null before use").

**Narrowing**: inside these forms, the value has type `T`:

- `if x { ... }` and `if x != null { ... }`: in the truthy branch;
- `while x { ... }` and `while x != null { ... }`: in the loop body (the
  condition is tested again before every iteration);
- `if !x { return ... }` / `if x == null { return ... }`: after the guard, for
  the rest of the enclosing block, when the guard block always leaves it
  (`return`, `break`, or `continue`);
- `if let y = x { ... }`: `y` is the non-null value in the then branch.

Only a binding narrows: a local, a parameter (`ref(T?)` and `mut(T?)` ones
included), or a module global. Testing a field (`if p.n`) leaves `p.n`
nullable, since the field can be reassigned through any alias of its record;
bind it first: `if let n = p.n { ... }`.

A narrowing never reaches past the branch, block, or loop body that holds
it: a guard inside a loop body or an `else` block narrows nothing after that
loop or `if`, since the loop may not run and the `else` may not be taken.

Assigning to a narrowed variable stores into its declared `T?`: `x = null` or
any other `T?` value is allowed and ends the narrowing from that point on,
including after a branch that may have made the assignment. Assigning a
non-null `T` keeps the variable narrowed. A branch arm that always returns
does not affect the code after the `if`; one that ends with `break` affects
only the code after the loop.

A narrowed module global, a `ref(T?)` or `ref(mut(T?))` parameter, or a local
that a closure assigns is re-widened after any call, since the call could
reassign it. Rendering a value counts as a call when its type declares a
`display` method: `print`, `println`, and a `"{v}"` segment run that method.

A narrowing made before a loop holds inside the loop only if no path through
the loop body can end it before the next iteration (a path that runs off the
end of the body or reaches `continue`). Otherwise, using the variable inside
the loop is an error until it is checked again there; testing it (`if x`,
`!x`, `x == null`) is always allowed. A test of a variable that is narrowed is
never folded statically: its truth comes from control flow, not from its type.

A closure may run at any later point, so it sees a narrowed variable as `T`
only when nothing can reassign it while the closure exists: a local that is
not assigned after the closure literal (or anywhere in a loop around it) and
that no closure assigns. Otherwise, and always for a module global or a
reference parameter, the closure sees the declared `T?` and must check it
itself.

### Absent fields

Accessing a member that a value's concrete type does not have is not an
error: by the
[member-presence rule](/references/reflection/#member-presence-xm-without-a-call)
it reads `null` (type `never?`), in a condition or not, so a condition over it
folds to its negative arm. This is what lets structurally typed code probe
optional fields (`if person.name { ... }`). Two exceptions:

- A field that only some of a _sum type's_ variants declare is an error to
  read from the sum (rather than from a matched variant), in a condition as
  well, because its presence would depend on the variant at run time.
- An anonymous record passed to an unannotated parameter must have every
  field the body uses outside a presence test; only a field used behind one
  may be absent (the parameter's row, see
  [Structural subtyping](#structural-subtyping)). With `println(p.name)` in
  the body, `f({ age: 3 })` is rejected for its missing field `name`.

A condition the type alone decides, whether an absent member (always false)
or a present, non-nullable one (always true), **folds statically**, and
everything the fold makes unreachable is left unchecked: the arm that is not
taken, and, when the taken arm always returns, the statements after the `if`.
That code contributes nothing to the instantiation: its `return`s do not join
the return type, and an `error(..)` there does not make it fallible. The back
end folds the same branch and never emits that code, so a generic body can
probe its argument and let each instantiation take the arm that fits it:

```
fun as_text(value) -> string {
    if value._components {        // a Path has this field; a string does not
        return value.to_string()  // for a string: dead, not checked
    }
    return value                  // for a Path: unreachable, not checked
}
```

An ordinary `bool` condition is not statically known, so it never folds; this
does not hide errors in code that can run.

## Result

`T!` is `Result<T, E>` over the `Result` declared in the prelude
(core/error.cz): an ordinary two-variant sum with `Ok { value }` and
`Err { error }`, resolved by normal scoping at every sugar site, so a module
may [shadow it](/references/syntax-sugar/#the-result-behind-fallibility). The
error payload type `E` is inferred from the function's error sources (all
error sites of one function must reconcile to one payload type).

- `error(x)` is a prelude function that builds
  `Err { error: Error { value: x, location: <call site>, frames: [] } }`. The
  payload is the prelude `Error` record, stamped with the caller's position
  through the implicit `Location` argument. Traces, `context`, and the
  rendering are specified in
  [Error traces](/references/syntax-sugar/#error-traces). The name is
  compiler-owned: no function declaration may redefine it (see
  [Identifiers and keywords](/references/syntax/#identifiers-and-keywords)).
- A function is _fallible_ when its body uses `error(...)` or a
  Result-operand `expr!`, or its declared return type is a Result. Every
  `error(...)` the body evaluates is an error source, whether its Result is
  returned, propagated, bound or dropped. In a fallible function, `return v`
  with a plain value wraps it as `Ok { value: v }` automatically; returning a
  Result value forwards its Ok payload without nesting. A forwarding `return`
  in a function whose return annotation ends in `!` also lifts a raw error
  payload into the prelude `Error`, stamped at the returned expression. An
  already-wrapped `Error` keeps its location and frames.
- The postfix **`!`** operator propagates: `expr!` unwraps an `Ok` or returns
  the `Err` early from the enclosing function. A propagated payload that is
  not already the prelude `Error` (a builtin's or plugin's plain string, for
  example) is **lifted** into one at the propagation site, which is what lets
  one body mix `error(..)` with `!`-forwarded builtin failures.
- `!` also accepts a **declared subtype** of the scope's Result
  (`type MyResult: Result`, see
  [Declared sum subtyping](/references/syntax-sugar/#declared-sum-subtyping)):
  the value is rebuilt as the parent at the operand and `!` proceeds on it.
- On a **NULLABLE** operand, `expr!` unwraps the value, and a null returns
  **null itself** early: the enclosing function's return type gains an outer
  `?` (it does not become fallible). A body mixing bare returns, `error(...)`,
  and a nullable `!` therefore infers `Result<T, E>?`: consume it by
  narrowing the `?` first, then matching the Result. An explicit non-nullable
  return annotation rejects a nullable `!` in the body.
- `!` is allowed inside any named function or closure whose return can carry
  the failure (an inferred return always can; see [Closures](#closures)),
  **at the module top level, and in `main`**. At those two entry points a
  failed `!` does not propagate (there is no caller to receive it): the
  program aborts on stderr with a non-zero exit, using the nested
  `[file:line:col] unhandled error:` trace whenever the payload is the
  prelude `Error`, including errors lifted at `!` or a forwarding `return`.
  Other payloads use the plain `runtime error: unhandled error: <payload>`
  line; a failed nullable unwrap uses the null message.
- Consume a Result by matching `Ok { value }` / `Err { error }`. A payload
  raised by `error(..)`, or lifted at `!` or a forwarding `return`, matches
  as the `Error` record:
  the original value is `error.value`, and `error.display()` renders the
  trace.
- A function that can only ever `error(...)` (no successful return) cannot be
  used where a value is required: reading its Ok payload -- a used
  `Ok { value }` binding, or `f()!` in a value position -- is a compile
  error. `f()!` as a statement, or a returned `f()`, only propagates the
  error and is allowed.

Separately, returns of `null` and returns of `T` in one function join to
`T?` (see [Inferred return types](#inferred-return-types)).

## Inferred return types

An unannotated function's return type is the **join** of the values its
`return`s hand back, decided per instantiation (each call site re-checks the
body with its argument types):

- numeric values join to the smallest type every one of them converts to
  value-preservingly (the [flow conversions](#flow-conversions)): `int32`
  with `int64` is `int64`, `int8` with `uint8` is `int16`, `int32` with
  `float64` is `float64`; `int64` with `float64` has no join;
- a numeric literal adapts to the join of the other returns when its value
  fits that type, otherwise it keeps its default type and takes part in the
  join: `return small` (an `int8`) with `return 100` is `int8`, with
  `return 300` it is `int32`;
- `null` and `T` join to `T?`;
- a [declared sum subtype](/references/syntax-sugar/#declared-sum-subtyping)
  and its parent join to the parent (the subtype value is rebuilt where it is
  returned);
- any other two different types have no join.

The join does not depend on the order of the `return`s, and a path the
instantiation never takes (an unselected type-test arm, a statically folded
member-presence test) contributes nothing. An instantiation whose returns
have no join is a compile error at the conflicting `return`, naming the call
that created it: `fun pick(c, n) { if c { return 1 } return n }` is fine for
`pick(false, big_int64)` (an `int64`) but rejected for `pick(false, "x")`.
The error payloads of one fallible instantiation must join the same way.

## Polymorphism and inference

- **Let-polymorphism**: `let id = (x) -> x` may be used at several types; each
  use instantiates the inferred scheme freshly and builds its own closure
  value. Only a binding of a closure literal generalizes (the _value
  restriction_): a `let` or `const` binding (local or module-level) without a
  type annotation, never reassigned, whose initializer is a closure literal
  with at least one unannotated parameter. The scheme generalizes only the
  type variables not shared with the enclosing scope: a parameter the body
  ties to a captured binding -- `(v) -> names.push(v)` with a captured
  `names` -- is fixed by the first use like any monomorphic value. See
  [Closures](#closures).
- **Function polymorphism**: an unannotated function is re-checked per call
  site with the concrete argument types, then compiled per instantiation. This
  is stronger than a single inferred scheme: `fun add1(x) { return x + 1 }`
  works for `int32`, `int64`, and `float64` callers alike.
- **`infer`** in a signature marks an inference hole explicitly; each
  occurrence is independent.
- **Generic records** need no type parameters: leave fields unannotated (or
  build containers empty) and each construction site fixes its own
  instantiation. Methods share the record's inferred parameters, so a
  container's `set`/`get` agree on the element type without a witness value.
- **`fun T.m(self) -> infer!`** declares a reflective template whose result
  type is fixed by each call site's expected type; see
  [Compile-time reflection](/references/reflection/#generic-decoders-with---infer).

There is **no explicit type-parameter syntax** (`<T>` does not exist).

### Type slots and refinements

A record can name its type parameters as **slots** (members declared with the
`type` keyword, `type slot`) and refer to them elsewhere with `Self.slot`. A
slot has no runtime storage: it never appears in the layout, in `fields()`, or
in a construction literal. It only names a type another field is expressed
over. (The spelling `slot: type` -- the `type` keyword as the member's
declared type -- is also accepted.)

```brass
type _Entry = {
    key
    value
}

type Map = {
    type key             // type slots: the key/value types, no storage
    type value
    entries: _Entry { key: Self.key, value: Self.value }?[]
    count: int64
}
```

`Base { field: T, ... }` is a **refinement**: it pins the named slots (and
fields) of a record, yielding a concrete instance. Only a record type can be
refined: a sum type has no slots, and the types of its unannotated payload
fields are inferred from each construction, so `Opt { v: int32 }` over a sum
`Opt` is a compile error. Written as the right-hand side of an alias
declaration it gives that instance a name:

```brass norun
type StringInts = Map { key: string, value: int64 }
```

- An omitted slot stays open (inferred), so a partly-refined alias is still
  generic in the slots it does not mention.
- A slot may be pinned to anything; a real field that already has a concrete
  type may only be refined to that same type (a mismatch is rejected).
- A refinement pins each slot or field at most once; anonymous record
  literals and `anonymous { ... }` types likewise need unique field names.
- The alias is not a new nominal: it unifies with any matching instance, so a
  witness-free value built by the container's constructor is accepted where
  the refined type is annotated.
- An alias also names its target where a construction or a conversion
  names a type: `Alias { .. }` builds a record of the target, `Alias.from(v)`
  converts to it, and a sum alias (`type L2 = L`) names the sum's variants
  (`L2.Nil`, `L2.Cons { .. }`, also in patterns). Through a refinement the
  result is the alias's instance: `Box64 { item: 3 }` and
  `Box64.from({ item: 3 })` with `type Box64 = Box { item: int64 }` hold an
  `int64`, a literal field value adapting to the pinned type as it does when
  the literal flows into a slot annotated `Box64`.
- Annotating a binding with the alias pins the container's types up front, so
  `let m: Counts = HashMap.new()` (with
  `type Counts = HashMap { key: string, value: int64 }`) is a usable
  `string -> int64` map: later stores are checked against the pinned value
  type, so a bare integer literal or an `int32` value stores as an `int64`
  (see [Literals](#literals)).

Field types are resolved like Hindley–Milner inference: each field and slot is
assigned a type variable and `Self.field` resolves to it. A field whose type
refers back to itself through the `Self.field` chain (`a: Self.b`,
`b: Self.a`) is a circular unification and is **rejected** by the occurs-check.

## Match exhaustiveness

An arm after an irrefutable arm is a compile-time error (`unreachable match
arm`). This includes `_`, a whole-value binding, and total record, tuple,
fixed-array, or singleton-sum patterns. A bare name that is not a unit variant
binds a new variable; it does not compare with an existing constant. When such
a binding makes later arms unreachable, the diagnostic notes an in-scope
constant with that name or suggests a similarly spelled variant. Use literal
patterns or explicit comparisons when testing constant values.

A `match` whose scrutinee is a sum type must either name every variant or
contain a catch-all arm (`_` or a whole-value binding). Variant patterns
apply directly to a nullable sum (`S?`) and are refutable there: `null`
matches none of them, so such a `match` must in addition cover `null`, with a
`null` arm or the catch-all, and `if let S.V { .. } = x` takes its `else` on
`null`. A variant arm counts as covering its variant only when all of its
field sub-patterns are irrefutable (a literal field pattern makes the arm
partial). Matches over non-sum values (integers, strings) are not
exhaustiveness-checked; add a `_` arm. A function with a declared non-void
return type must return a value on every path (`while true` without `break`
counts as diverging).

Return-flow analysis follows divergence through evaluated positions such as
assignment right-hand sides and interpolation segments. Merely constructing a
closure whose body returns does not make the enclosing path diverge.

## Definite assignment

An annotated `let` inside a function or block may omit its initializer
(`let p: Point`); a module-level `let` cannot, since it defines a global. The
binding must then be definitely assigned before use:

- assigning the whole binding completes it;
- for a record type whose field skeleton is default-constructible (numbers,
  bool, string, nullable, arrays, tuples, and records of those, not sums or
  functions), assigning **every field individually** also completes it;
- branches join by intersection (both arms must assign); paths that return or
  diverge drop out;
- a `for field in fields(x)` loop that assigns `x[field]` on every non-exiting
  path counts as assigning all fields (see [Reflection](/references/reflection/));
- reading the binding, or capturing it in a closure, before completion is a
  compile error. `typeof(x)` and `fields(x)` only read the type and are
  allowed;
- the same checks apply inside closure bodies and the blocks of top-level
  code, and to reads nested in assignment right-hand sides or interpolation
  segments.

## Recursion and program order

- Recursion, direct or **mutual**, needs no annotations. A recursive call
  types against the function's return annotation when it has one; otherwise
  each instantiation's return is inferred from the values the function (or
  its cycle) returns that do not come from the recursion itself (`return 1`
  in a factorial, `return true` in `is_even`/`is_odd`). When every value a
  function returns comes from its own recursion, nothing determines the type
  and the call is rejected with a request to annotate the return type.
- **Polymorphic recursion** is not supported. A function may call itself at
  other concrete argument types (each set of types is one instance), but not
  with its own parameter wrapped in a larger type (`f([x])` inside `f(x)`):
  every level would need a new instance, so such a call is a compile error.
- Functions and types may be used textually before their definitions. A
  module-level **binding** may not: globals initialize in order, and reading
  one before its initializer has run is a compile error, also when the read
  happens inside a function or method an earlier initializer calls. A closure
  literal an earlier initializer evaluates counts as reading the globals its
  body names, since it may be called before they are initialized.

## Closures

Closures **capture by reference**: the closure sees (and may mutate) the live
binding, and mutations through the closure are visible outside. A closure's
parameter and return types are inferred (annotations optional). A closure
parameter, like any local binding, shadows function names other than the
language constructs (see
[Identifiers and keywords](/references/syntax/#identifiers-and-keywords)).

How a closure's types are fixed:

- A closure literal checked where a function type is expected (an annotated
  parameter, field, binding or return) takes its parameter types from that
  type, and its result is converted into the expected result (a body
  returning `int32` where `int32?` is expected yields a present `int32?`).
  Record, sum and array parameter types work like primitive ones.
- A let-polymorphic binding (see
  [Polymorphism](#polymorphism-and-inference)) is instantiated at each use:
  `let show = (x) -> "<{x}>"` maps over an `int32[]` and a `string[]` alike.
  Each use is compiled at its own instantiation.
- Every other closure value -- a reassigned binding, a parameter, a closure
  passed directly as an argument, stored in a field or array, or returned --
  is **monomorphic**: its first application fixes its open parameter types,
  and every other application must agree with them (the arguments flow into
  the fixed types with the usual conversions, so an `int32` argument widens
  into an `int64` parameter). For any closure value bound by `let` -- a
  literal, a call's result (`let r = make()`), an element
  (`let g = fs[0]`), or a recursive closure assigned to a binding declared
  first -- a still-open parameter whose arguments at the binding's direct
  calls in the rest of its block are all numbers (or `null`) is fixed at
  their [join](#inferred-return-types) instead, whatever the order of the
  calls: `f(an_int32)` followed by `f(an_int64)` makes it an `int64` just
  like the reverse order, and every call's result is the closure's result at
  that type.
- A closure returned from a function is compiled with each instance of that
  function, so its parameter types are fixed by the end of the instance's
  check when its body determines them -- `(x) -> x + n` with `n: int32`
  takes `int32` -- and otherwise by its uses, as above. A closure whose
  parameter types nothing in the program determines is rejected with a
  request to annotate them.
- An unannotated parameter used in arithmetic next to a numeric literal
  types the operation by the argument (the literal adapts): `(x) -> x * 2`
  returns its argument's type at each instantiation.
- A function named as a value is a closure whose type is the function's own
  signature.

A `let` initializer cannot refer to the binding it defines, so a recursive
closure is assigned to a binding declared first:
`let fact = (n: int32) -> 0` then
`fact = (n: int32) -> { ... fact(n - 1) ... }`. The closure captures the
binding itself, and each call reads the closure currently stored in it.

Closures may be **fallible**, exactly like a named function whose unannotated
body raises: a body that uses `error(...)` or a Result-operand `!` returns
`Result<T, E>`, a bare `return v` (or an expression body's value) is the Ok
payload, and the null case of a nullable-operand `!` propagates null (the
return becomes `T?`). There is no `!` sugar on closure types -- the `Result`
appears directly in the inferred function type, and the caller unwraps it with
`!` or a `match`:

```brass
let parse = (s: string) -> int32.parse(s)!
let n = parse("41")!            // parse: (string) -> Result<int32, Error>
```

A fallible closure also works through a generic (unannotated) higher-order
parameter, where each call's `Result` is an ordinary value:
`xs.map((v) -> v.lookup(k)!.name)` yields a `Result[]` holding one `Ok` or
`Err` per element; the failure does not propagate out of `map` itself.
`spawn` requires a closure returning `void`, so it rejects a fallible
closure.

## Concurrency typing

`spawn(f)` requires a zero-parameter closure whose return type is `void` (or
still open), and returns `void`; `with(c, f)` requires a one-parameter closure
and returns the closure's result; `sync()` takes nothing. Ownership analysis of
captured values happens after type checking; see the
[concurrency reference](/references/concurrency/).
