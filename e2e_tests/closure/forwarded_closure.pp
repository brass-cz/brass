// A closure typed through a FORWARDING wrapper: `g` never calls `handler`, it
// hands it to `f`, whose annotation carries the call contract. The back end types
// a closure from how it is used -- an in-body call, or the parameter a
// higher-order callee calls it as -- and neither reached a merely-forwarding
// callee, so the closure's temporary had no type at all ("cannot infer the type
// of an expression temporary"). The probe now follows the forward, across more
// than one hop and at any argument position.
fun f(handler: (int32) -> void) {
    handler(1)
}

fun g(handler) {
    f(handler)
}

fun two(prefix: string, handler: (int32, string) -> void) {
    println(prefix)
    handler(2, "x")
}

fun mid(handler) {
    two("pre", handler)
}

fun outer(handler) {
    mid(handler)
}

fun apply(x: int32, op) {
    return op(x)
}

fun through(op) {
    return apply(3, op)
}

g((v) -> { println(v) })
outer((n, s) -> { println("{n}/{s}") })
println(through((v) -> v * 2))
