// Uniform Function Call Syntax: `recv.f(args)` resolves to the
// free function `f(recv, args)` when the receiver has no method `f`. The
// receiver type is checked against the function's first parameter, and the
// inferred return type flows to the caller.

type Vec2 = {
    x: float64
    y: float64
}

fun length_sq(v: Vec2) -> float64 {
    return v.x * v.x + v.y * v.y
}

fun scaled(v: Vec2, k: float64) {
    return Vec2 { x: v.x * k, y: v.y * k }
}

fun main() {
    let v = Vec2 { x: 3.0, y: 4.0 }

    // Method-call syntax dispatches to the free functions above.
    let sq: float64 = v.length_sq()
    println("length_sq = {sq}")

    let big = v.scaled(2.0)
    println("scaled = ({big.x}, {big.y})")
}
