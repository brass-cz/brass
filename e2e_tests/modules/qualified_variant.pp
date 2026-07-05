// Qualified variant construction: `alias.Sum.Variant { .. }` works through a
// module import, including match patterns on the result.
import shapelib

fun main() {
    let c = shapelib.Shape.Circle { r: 2.5 }
    println(shapelib.describe(c))
    println(shapelib.describe(shapelib.Shape.Dot))
}
