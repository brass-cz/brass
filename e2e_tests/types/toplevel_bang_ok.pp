// `!` is allowed at the module top level: on success it unwraps in place,
// for a `Result` and for a nullable operand alike.
fun half(n: int32) -> int32! {
    if n % 2 != 0 {
        return error("odd: {n}")
    }
    return n / 2
}

fun first_over(a: int32[], want: int32) -> int32? {
    for x in a {
        if x > want {
            return x
        }
    }
    return null
}

let h = half(10)!
println("half {h}")
let v = first_over([1, 2, 3], 1)!
println("over {v}")
