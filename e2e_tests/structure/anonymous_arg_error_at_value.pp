// A callee-body failure caused by an anonymous argument is reported AT THE
// VALUE with the constraint the body derived, not at a span inside the callee.
fun get_x(p) -> int32 {
    return p.x
}

fun main() {
    println(get_x({ y: 1 }))
}
