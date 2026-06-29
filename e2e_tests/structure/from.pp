// `T.from(v)` converts any structure with at least T's fields into a T value.
type Point = { x: int32, y: int32 }

let big = { x: 1, y: 2, z: 3 }
let p = Point.from(big)
println(p.x)
println(p.y)
