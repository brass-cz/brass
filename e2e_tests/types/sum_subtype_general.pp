// Declared sum subtyping on ordinary (non-Result) sums: a child covering the
// parent's variant set with wider variants coerces at annotated flow sites
// (here a parameter), dropping the extra fields.
type Shape =
    | Circle {
        r: int32
    }
    | Square {
        side: int32
    }

type NamedShape: Shape =
    | Circle {
        r: int32
        label: string
    }
    | Square {
        side: int32
        label: string
    }

fun area2x(s: Shape) -> int32 {
    return match s {
        Circle { r } => 6 * r * r
        Square { side } => 2 * side * side
    }
}

fun main() {
    let c = NamedShape.Circle { r: 2, label: "c" }
    println(area2x(c))
    println(area2x(NamedShape.Square { side: 3, label: "s" }))
    println(match c {
        Circle { r, label } => "{label}:{r}"
        Square { side, label } => "{label}:{side}"
    })
}
