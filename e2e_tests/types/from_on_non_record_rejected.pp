// `T.from(v)` builds `T` out of `v`'s FIELDS. A sum value has none, so the
// conversion could only ever yield null -- a program the checker used to accept
// and that then always took its failure path at run time.
type Shape =
    | Circle { r: int64 }
    | Square { w: int64 }

type Dims = {
    r: int64
}

const s = Shape.Circle { r: 2 }
if let d = Dims.from(s) {
    println(d.r)
} else {
    println("no")
}
