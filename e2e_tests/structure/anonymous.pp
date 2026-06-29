// `{ field: value, ... }` in expression position is an anonymous structure value;
// `anonymous { field: T, ... }` is the matching structural type.
fun first(p: anonymous { x: int32, y: string }) -> int32 {
    return p.x
}

let pt = { x: 10, y: "ten" }
println(pt.x)
println(pt.y)
println(first({ x: 7, y: "seven" }))
println({ a: 1, b: true })
