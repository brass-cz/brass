// Arithmetic between mixed numeric types implicitly converts to a common type:
// int op int -> wider width; int op uint -> signed; int op float -> that float;
// float op float -> wider width.
let a: int32 = 3
let b: int64 = 10
let c: uint32 = 5
let f: float64 = 2.5

println(a + b)   // int32 + int64 -> int64
println(a + c)   // int32 + uint32 -> int32
println(a + f)   // int32 + float64 -> float64
println(a * f)   // int32 * float64 -> float64
println(a < f)   // mixed comparison

// An integer literal in a float context becomes a float.
for e in [1.1, 2.2, 3.3] {
    println(e * 2)
}
