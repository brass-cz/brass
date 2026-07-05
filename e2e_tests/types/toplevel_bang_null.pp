// A null propagated by `!` at the top level aborts the program with an
// error, exactly like inside `main`: the null has nowhere to go, and
// silently succeeding would hide the failure.
fun first_over(a: int32[], want: int32) -> int32? {
    for x in a {
        if x > want {
            return x
        }
    }
    return null
}

println("looking")
let v = first_over([1, 2, 3], 9)!
println("unreachable {v}")
