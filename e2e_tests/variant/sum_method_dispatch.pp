// A method declared on a sum type (`fun Shape.area`) applies to every variant
// and is callable on a sum-typed value; methods can call sibling methods
// through `self`. Pins whole-sum method dispatch end to end.
type Shape =
    | Point
    | Circle { r: float64 }
    | Rect { w: float64, h: float64 }

fun Shape.area(self) -> float64 {
    return match self {
        Shape.Point => 0.0,
        Shape.Circle { r } => 3.14159 * r * r,
        Shape.Rect { w, h } => w * h,
    }
}

fun Shape.describe(self) -> string {
    return "area={self.area()}"
}

fun main() {
    let shapes = [Shape.Point, Shape.Circle { r: 1.0 }, Shape.Rect { w: 2.0, h: 3.0 }]
    for s in shapes {
        println(s.describe())
    }
}
