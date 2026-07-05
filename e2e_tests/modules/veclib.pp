// Library module used by qualified_import.pp; running it standalone does
// nothing (no main, no top-level output).
type Vec2 = {
    x: float64
    y: float64
}

fun Vec2.new(x: float64, y: float64) {
    return Self { x: x, y: y }
}

fun dot(a: Vec2, b: Vec2) -> float64 {
    return a.x * b.x + a.y * b.y
}
