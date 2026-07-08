import std.collections.{ HashMap }

type Inner = { a: int64, b: int64 }
type Outer = { label: string, inner: Inner }

// Nested fields-loops: the outer loop's copies each contain the inner loop,
// whose spans are shifted again; both levels expand independently.
fun sum_inner(o: Outer) -> int64 {
    let total: int64 = 0
    for f in fields(o.inner) {
        total = total + o.inner[f]
    }
    return total
}

// The loop variable as a HashMap key: the string decay in an argument position.
fun to_map(p: Inner) {
    const m = HashMap.new()
    for f in fields(p) {
        m.set(f, p[f])
    }
    return m
}

fun main() {
    const o = Outer { label: "L", inner: Inner { a: 10, b: 32 } }
    println(sum_inner(o))
    const m = to_map(o.inner)
    if let v = m.get("b") {
        println(v)
    }
}
