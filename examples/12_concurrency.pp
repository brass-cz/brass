// Concurrency: the only primitives are `spawn(f)` and `with(cown, f)`. The
// compiler/runtime decides ownership (move/freeze/cown) automatically; the
// programmer never writes those. Here two spawned tasks update a shared
// counter, and `with` acquires it to read the result.

type Counter = {
    count: int32
    total: int32

    add(self, n: int32) {
        self.count += 1
        self.total += n
    }
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
