// A module import (`import modules.veclib` without braces) exposes the
// module's exports qualified by the last path segment: type positions,
// static calls, record literals, and free functions.
import veclib

fun main() {
    let a: veclib.Vec2 = veclib.Vec2.new(1.0, 2.0)
    let b = veclib.Vec2 { x: 3.0, y: 4.0 }
    println(veclib.dot(a, b))
}
