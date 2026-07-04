---
title: "Concurrency"
description: "The concurrency primitives, inferred ownership, and static restrictions."
---

:::caution
Concurrency is **experimental**. It executes on the native (JIT) runtime
only; the REPL interpreter refuses `spawn`/`with`/`sync` at runtime.
:::

## The primitives

The complete programmer-facing surface is three builtin functions — there is
no `async`/`await`, no explicit locks, threads, or channels, and no ownership
annotations:

| Builtin      | Type                    | Behavior                                                           |
| ------------ | ----------------------- | ------------------------------------------------------------------ |
| `spawn(f)`   | `(() -> void) -> void`  | run a zero-parameter closure on another thread                     |
| `sync()`     | `() -> void`            | barrier: join every task spawned so far                            |
| `with(c, f)` | `(cown, (T) -> U) -> U` | acquire the shared object `c`, run `f` with it, yield `f`'s result |

Spawned tasks are also joined at the end of `main`. Use `sync()` before
reading values a task mutates; without it the read may run ahead of the task.

## Inferred ownership

The compiler decides how each captured value crosses the spawn boundary; the
programmer never writes `move`/`freeze`/`cown`:

- a captured **primitive** (number, bool) is copied by value into the task;
- a captured **heap object** (record, array, ...) that is shared with — and
  mutated by — concurrent code is promoted to a _cown_ (concurrent owner): a
  guarded object whose accesses are serialized by its lock;
- when the spawning function itself keeps using a promoted object, every one
  of its accesses is auto-guarded by the same lock, and the compiler emits a
  warning suggesting explicit `with(cown, f)` acquisition for finer-grained
  control. The lock is reentrant, so nested guarded accesses (including
  methods that mutate `self`) do not deadlock.

`with(c, f)` acquires `c`'s lock for the duration of `f`. The group form used
internally acquires multiple cowns in address order, so a consistent lock
order is maintained.

## Static restrictions

These are compile errors today:

- `spawn`'s argument must be a **closure literal**, or a local variable
  directly bound to one — not a function reference, a call result, or a
  parameter (the ownership pass must see the closure body).
- The closure must take **zero parameters**; `with`'s closure exactly one.
- A spawned task may not read or write a **module global** that any code
  writes; share state through captured objects instead.
- `spawn` at the top level (in a module initializer, outside any function) is
  unsupported.
- Nested spawns inside an already-spawned closure are analyzed like the outer
  one; a shape the pass cannot analyze is rejected rather than left unguarded.

## Example

```prepoly norun
type Counter = {
    count: int32
}

fun Counter.add(self) {
    self.count += 1
}

fun main() {
    let counter = Counter { count: 0 }

    spawn(() -> {
        for i in [0..1000] {
            counter.add()
        }
    })
    spawn(() -> {
        for i in [0..1000] {
            counter.add()
        }
    })

    sync()

    with(counter, (c) -> {
        println(c.count)   // 2000: both increments serialized by the cown lock
    })
}
```
