// A renamed TYPE import (`import m.{ Vec2 as V }`) works everywhere the bare
// name would: record construction, a type annotation, a static call, and a
// method call on the value.
import renametylib.{ Vec2 as V }

fun main() {
    let v = V { x: 1.0, y: 2.0 }
    let w: V = V.new(3.0, 4.0)
    println(v.x + w.y)
    println(v.add(w).x)
}
