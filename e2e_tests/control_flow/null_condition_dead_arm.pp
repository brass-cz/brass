// A bare `null` flowing into an unannotated `if` condition. The parameter is
// monomorphized to `never?` (a value that can only be null), so the truthy arm
// -- which narrows it to `never` and would multiply -- is statically dead: the
// checker tolerates it and the back end skips emitting it. A passed value takes
// the opposite, always-true arm. Both backends must run this identically.
fun double(a) {
    if a {
        return a * 2
    } else {
        return error("null")
    }
}

fun main() {
    println(double(2))
    println(double(null))
}
