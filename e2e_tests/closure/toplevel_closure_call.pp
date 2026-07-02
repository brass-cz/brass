// A closure bound at module top level is a module global holding a function
// value; calling it works both from later top-level statements and from
// function bodies (the call loads the global and dispatches indirectly).
let inc = (n: int32) -> n + 1

println(inc(1))

fun main() {
    println(inc(41))
}
