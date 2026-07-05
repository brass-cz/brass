// Library module with a sum type, used by qualified_variant.pp.
type Shape =
    | Circle { r: float64 }
    | Dot

fun describe(s: Shape) -> string {
    return match s {
        Shape.Circle { r } => "circle {r}",
        Shape.Dot => "dot",
    }
}
