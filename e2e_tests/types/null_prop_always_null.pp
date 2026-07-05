// `!` works on any nullable, Result or not -- including a binding that is
// always null. The inner `a!` returns null from `f` (its return joins to
// `int32?`), and the outer `f()!` at the top level aborts with the null
// propagation error.
fun f() {
    let a = null
    if false {
        return 1
    } else {
        a!
    }
}

f()!
println("unreachable")
