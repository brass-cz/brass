// An unannotated fallible function that returns an already-fallible value
// forwards the Result whole -- its type is Result<T, E>, never a nested
// Result<Result<T, E>, E>. The back ends Ok-wrap only bare return values, so
// the checker nesting this used to describe a value the program never built;
// a compensating double-`!` then reinterpreted the payload record as a
// Result and crashed (found via an HTTP fetch whose status field 200 was
// retained as a pointer).
type Point = {
    x: int32
    y: int32
}

fun make(fail: bool) -> Point! {
    if fail { error("nope")! }
    return Point { x: 1, y: 2 }
}

// Forwards make()'s Result while having error sites of its own.
fun forward(fail: bool) {
    if false { error("own failure")! }
    return make(fail)
}

// A single `!` must unwrap the forwarded Result completely.
const p = forward(false)!
println(p.x + p.y)

// The forwarded Err arrives as the same single-layer Result.
match forward(true) {
    Ok { value } => println("unexpected ok"),
    Err { error } => println("err: {error}"),
}

// Scalar payloads forward identically.
fun make_n(fail: bool) -> int32! {
    if fail { error("no number")! }
    return 41
}

fun forward_n(fail: bool) {
    if false { error("own failure")! }
    return make_n(fail)
}

println(forward_n(false)! + 1)
