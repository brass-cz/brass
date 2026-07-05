// Variants constructed through a module qualifier can be matched with the
// same qualified spelling: the pattern's qualifier segments are consumed and
// the variant is resolved against the scrutinee's type.
import shapelib

fun main() {
    let c = shapelib.Shape.Circle { r: 2.0 }
    match c {
        shapelib.Shape.Circle { r } => println("circle {r}"),
        shapelib.Shape.Dot => println("dot"),
    }
    match shapelib.Shape.Dot {
        shapelib.Shape.Circle { r } => println("circle {r}"),
        shapelib.Shape.Dot => println("dot"),
    }
}
