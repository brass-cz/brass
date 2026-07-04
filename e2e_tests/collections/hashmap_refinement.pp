// The standard-library HashMap declares `key`/`value` type slots, so a
// refinement alias names a concrete instantiation. A witness-free map built with
// `HashMap.new()` and populated with `string` keys and `int64` values unifies
// with the refined `StringInts` type and is accepted where it is annotated.

import std.collections.hashmap.{ HashMap }

type StringInts = HashMap {
    key: string,
    value: int64,
}

fun total(m: StringInts) -> int64 {
    let sum: int64 = 0
    for v in m.values() {
        sum += v
    }
    return sum
}

fun main() {
    let m = HashMap.new()
    m.set("a", 10)
    m.set("b", 32)
    println(total(m))
    println(m.get("a"))
}
