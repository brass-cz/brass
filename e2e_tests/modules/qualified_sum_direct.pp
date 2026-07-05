// Constructing a sum type directly through a module qualifier is rejected
// with the variant hint and a source span, not a span-less back-end error.
import shapelib

fun main() {
    let c = shapelib.Shape { r: 1.0 }
    println(1)
}
