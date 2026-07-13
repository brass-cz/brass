// `T.from(v)` builds `T` out of `v`'s FIELDS, and accepts a `v` of any type: one
// that has none of them answers null rather than failing to compile. A SUM value
// is such a `v` -- its fields live in its variants, which the conversion does
// not read -- so this takes the null path at run time. (Rejecting it statically,
// as the checker once did, also rejected the useful shape: a function that asks
// "is this argument a T?" about a value whose type differs per call site.)
type Shape =
    | Circle { r: int64 }
    | Square { w: int64 }

type Dims = {
    r: int64
}

const s = Shape.Circle { r: 2 }
if let d = Dims.from(s) {
    println("built {d.r} from a sum value")
} else {
    println("a sum value has no fields to build from")
}
