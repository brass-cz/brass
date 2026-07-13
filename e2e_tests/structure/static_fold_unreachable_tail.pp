// A condition the type alone decides folds statically -- an absent member is
// always false, a present non-nullable one always true -- and the code the fold
// makes unreachable is left unchecked. That covers the arm not taken AND, when
// the taken arm always returns, the statements after the `if`. The back end
// folds the same branch and never emits either, so one generic body can serve
// argument types that could not both type-check its whole text.
//
// Without the tail rule, `return value` below would be checked with `value` a
// `Point` (where a string is required) for the Point instantiation, even though
// the branch above it has already returned.
type Point = {
    x: int32
    y: int32
}

fun Point.render(self) -> string {
    return "({self.x}, {self.y})"
}

// The tail is dead for a Point (the `if` returns) and live for a string (the
// `if` folds away).
fun as_text(value) -> string {
    if value.x {
        return value.render()
    }
    return value
}

// The same fold, guarding the other way round: `chars` is a string method a
// Point does not have.
fun describe(value) -> string {
    if value.chars {
        return "the string {value}"
    }
    return "the point {value.render()}"
}

fun main() {
    println(as_text(Point { x: 1, y: 2 }))
    println(as_text("already text"))
    println(describe(Point { x: 3, y: 4 }))
    println(describe("hello"))

    // A `bool` condition is not statically known, so nothing after it is
    // treated as unreachable -- ordinary control flow is unaffected.
    println(pick(true))
    println(pick(false))
}

fun pick(c: bool) -> string {
    if c {
        return "then"
    }
    return "tail"
}
