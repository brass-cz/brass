// A failed `!` in the entry `main` aborts the same way as at the top level:
// the error is printed and the process exits non-zero. `Null` results
// propagated from a callee's nullable `!` abort with the null message.
fun half(n: int32) -> int32! {
    if n % 2 != 0 {
        return error("odd: {n}")
    }
    return n / 2
}

fun main() {
    let ok = half(10)!
    println("half {ok}")
    let bad = half(3)!
    println("unreachable {bad}")
}
