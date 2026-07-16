type T = {
    x: int32
}

type Shape =
    | Circle { r: int32 }
    | Square { side: int32 }

fun T.get(self) -> int32 {
    return self.x
}

fun Shape.area(self) -> int32 {
    match self {
        Circle { r } => { return 3 * r * r }
        Square { side } => { return side * side }
    }
}

// One generic body dispatches on declared-method presence: the record arm,
// the sum arm, and the plain arm each compile only for the instantiation
// that has (or lacks) the member.
fun describe(v) -> string {
    if v.get {
        return "get {v.get()}"
    } else if v.area {
        return "area {v.area()}"
    }
    return "plain"
}

fun main() {
    println(describe(T { x: 7 }))
    println(describe(Shape.Circle { r: 2 }))
    println(describe(3))
    // A concrete receiver folds the same way inside a non-generic body.
    let s = Shape.Square { side: 3 }
    if s.area {
        println(s.area())
    }
}
