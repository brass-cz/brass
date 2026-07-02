// Automatic numeric conversion at *flow* positions: a numeric value converts
// when assigned, passed, returned, compound-assigned, or stored into a numeric
// position of a different type (int widths/signedness, int -> float). See
// numeric_conversions.pp for the operator-level conversions.

fun widen(x: int64) -> int64 {
    return x
}

fun narrow(x: int32) -> int32 {
    return x
}

fun halve(x: float64) -> float64 {
    return x / 2.0
}

fun as_nullable(x: int32) -> int64? {
    if x > 0 {
        return x
    }
    return null
}

type Counter = {
    total: int64
}

fun bump(c: ref(mut(Counter)), by: int32) {
    c.total += by
}

fun main() {
    // Assignments widen and (lossily) narrow.
    let a: int32 = 5
    let b: int64 = a
    println(b)
    let back: int32 = b
    println(back)
    // Arguments and returns convert; 2^32 + 5 truncates to 5 through int32.
    let big: int64 = 4294967301
    println(widen(a))
    println(narrow(big))
    println(halve(a + 2))
    // Compound assignment converts the operand at the write-back.
    let t: int64 = 1
    t += a
    println(t)
    // Conversion into a nullable position wraps at the element type.
    let m = as_nullable(a)
    if m {
        println(m * 2)
    }
    // A record field annotated int64 accepts int32 values.
    let c = Counter { total: 5 }
    bump(c, 3)
    println(c.total)
    // Array literals build at the annotated element width.
    let xs: int64[] = [1, 2, 3]
    xs[0] = a
    println(xs)
    let bytes: uint8[] = [200, 100, 55]
    println(bytes[0] + bytes[2])
    // The stdlib int limits: a 64-bit constant keeps its magnitude.
    println(INT64_MAX)
    let top: int64 = INT64_MAX
    println(top - INT32_MAX)
    // A mixed-magnitude bracket literal is a tuple; each position keeps its
    // own width (the int64 element must not truncate to the int32 default).
    let pair = [1, 9223372036854775807]
    println(pair[1])
    // An int64-typed value matches a 64-bit literal pattern.
    match top {
        9223372036854775807 => println("max")
        _ => println("other")
    }
}
