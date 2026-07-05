// `import veclib.dot` (no braces) imports the one trailing name, exactly
// like `import veclib.{ dot }`.
import veclib.dot
import veclib.Vec2

fun main() {
    println(dot(Vec2 { x: 1.0, y: 1.0 }, Vec2 { x: 2.0, y: 3.0 }))
}
