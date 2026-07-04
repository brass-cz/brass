// A refinement may pin a type slot to anything, but a real field that already
// has a concrete type may only be refined to that same type. `count` is declared
// `int64`, so refining it to `string` is rejected.

type Box = {
    key: type
    value: type
    count: int64
}

type Bad = Box { count: string }

fun main() {
    println(1)
}
