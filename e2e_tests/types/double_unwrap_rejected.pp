// A forwarded Result is single-layer, so unwrapping it twice is a static
// error (the second `!` has a plain record operand). Before forwarding was
// fixed, the checker typed this nested and `!!` was the only way to satisfy
// it -- and then crashed at runtime.
type Point = {
    x: int32
    y: int32
}

fun make() -> Point! {
    if false { error("nope")! }
    return Point { x: 1, y: 2 }
}

fun forward() {
    if false { error("own failure")! }
    return make()
}

const p = forward()
println(p!!)
