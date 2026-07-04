# Concurrency

> Concurrency is **experimental** and runs on the native (JIT) runtime only.

prepoly's concurrency surface is three functions — there is no `async`, no
locks, and no ownership annotations to write:

- `spawn(f)` runs a zero-argument closure on another thread.
- `sync()` waits for all spawned work so far.
- `with(shared, f)` acquires a shared object and passes it to the closure.

The compiler infers ownership of captured values automatically: values shared
between tasks are promoted to guarded objects behind the scenes, and access to
them is serialized.

```prepoly
type Counter = {
    count: int32
    total: int32
}

fun Counter.add(self, n: int32) {
    self.count += 1
    self.total += n
}

fun main() {
    let nums1 = [1, 2, 3]
    let nums2 = [4, 5, 6]
    let counter = Counter { count: 0, total: 0 }

    spawn(() -> {
        for n in nums1 {
            counter.add(n)
        }
    })
    spawn(() -> {
        for n in nums2 {
            counter.add(n)
        }
    })

    sync()

    // Acquire the shared counter to read its final state.
    with(counter, (c) -> {
        println("count = {c.count}, total = {c.total}")
    })
}
```

```
count = 6, total = 21
```

Both tasks mutate the same `counter`; the compiler notices the shared capture
and guards it, so the updates do not race. It also prints a warning telling
you that every access to `counter` is auto-guarded — acquiring the object
explicitly with `with(cown, f)` gives finer-grained control and silences it.
`sync()` is the barrier that makes the spawned work's effects observable —
without it, the final read could run ahead of the tasks. Spawned work is
otherwise joined at the end of `main`.

Current restrictions (enforced as compile errors): `spawn` takes a closure
literal (or a local bound to one) with zero parameters; a spawned task may not
write module globals; and spawning at the top level (outside a function) is
unsupported. See the [concurrency reference](references/concurrency.md) for
details.
