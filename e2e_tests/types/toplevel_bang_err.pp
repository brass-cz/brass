// A failed `!` at the top level aborts the program, printing the error
// payload -- there is no caller to propagate a Result to.
fun half(n: int32) -> int32! {
    if n % 2 != 0 {
        return error("odd: {n}")
    }
    return n / 2
}

println("before")
let h = half(7)!
println("unreachable {h}")
