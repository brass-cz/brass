// Higher-order functions: closures passed as arguments are called as the local
// value even when their parameter name matches a global function, and the
// inferred result type flows to the caller.

fun apply_twice(f, x) {
    return f(f(x))
}

// A global function whose name collides with the closure parameter below.
fun step(n: int32) -> int32 {
    return n + 100
}

fun run(step) {
    // `step` here is the closure parameter, not the global function.
    return step(1)
}

fun main() {
    let inc = (n: int32) -> n + 1
    println("apply_twice = {apply_twice(inc, 10)}")

    let doubled = run((x: int32) -> x * 2)
    println("run = {doubled}")
}
