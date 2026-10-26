// An array literal checked against a nullable-element slice annotation
// (`int32?[]`) propagates the element type to each element: a `null` element is a
// valid nullable, and a plain integer widens to the nullable element. Without the
// annotation flowing in, `[4, 1, 5, null, 65]` (mixed `int32`/`null`) would be
// inferred independently and rejected.
const with_null: int32?[] = [4, 1, 5, null, 65]
const all_present: int32?[] = [4, 1, 5, 65]

// A nullable-element parameter accepts both plain and null-containing literals
// at the call site, and its elements narrow like any other nullable.
fun sum_present(xs: int32?[]) -> int32 {
    let total: int32 = 0
    for x in xs {
        if x {
            total += x
        }
    }
    return total
}

fun main() {
    println(with_null)
    println(all_present)
    // The elements are usable as `int32?`: a null check narrows to `int32`.
    let first = with_null[3]
    if first {
        println("present: {first}")
    } else {
        println("absent")
    }
    // The same annotation works on an in-function `let`: the literal's elements
    // are built as nullable cells, not the bare `int32` representation (which
    // previously crashed the JIT on the first element read).
    let a: int32?[] = [1, 2, 3]
    println(a)
    let head = a[0]
    if head {
        println("head: {head}")
    }
    // Null and value elements mix, and element stores accept both.
    let b: int32?[] = [10, null, 30]
    b[1] = 20
    b[2] = null
    println(b)
    // Literals flow into a nullable-element parameter directly.
    println(sum_present([7, null, 8]))
    println(sum_present(a))
}
