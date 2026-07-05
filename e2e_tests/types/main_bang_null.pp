// A null propagated by `!` inside `main` ABORTS with an error (unlike the
// module top level, where it terminates the program successfully): `main` is
// an ordinary function whose null has nowhere to go, so silently succeeding
// would hide the failure.
fun find(a: int32[], want: int32) -> int32? {
    for x in a {
        if x == want {
            return x
        }
    }
    return null
}

fun main() {
    println("start")
    let v = find([1, 2, 3], 9)!
    println("unreachable {v}")
}
