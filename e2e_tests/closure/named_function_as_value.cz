// A top-level function used as a first-class value (not called): it is passed to
// a higher-order function and stored in a local. Calling an unannotated parameter
// (`apply`'s `f`) infers it as a function, and a bare function name is eta-expanded
// into a forwarding closure, so both the bare name and a wrapping lambda work.
fun id(x) {
    return x
}

fun inc(x) {
    return x + 1
}

fun apply(f, x) {
    return f(x)
}

fun main() {
    println(apply(id, 3))            // 3
    println(apply((x) -> id(x), 3))  // 3
    println(apply(inc, 10))          // 11
    let g = inc
    println(g(41))                   // 42
}
