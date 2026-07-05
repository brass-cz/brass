// A renamed SUM type import constructs variants and matches on them under
// the local name.
import shapelib.{ Shape as Sh }

fun main() {
    let c = Sh.Circle { r: 2.0 }
    match c {
        Sh.Circle { r } => println("circle {r}"),
        Sh.Dot => println("dot"),
    }
    let d = Sh.Dot
    match d {
        Sh.Circle { r } => println("circle {r}"),
        Sh.Dot => println("dot"),
    }
}
