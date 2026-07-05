// `!` on a NULLABLE operand unwraps the value; a null returns null from the
// enclosing callable, so its inferred return type gains an outer `?`
// (`pick` is `(int32) -> int32?` -- no Result is involved).
fun first_over(a: int32[], want: int32) -> int32? {
    for x in a {
        if x > want {
            return x
        }
    }
    return null
}

fun pick(limit: int32) {
    let v = first_over([1, 2, 3], limit)!
    return v + 100
}

let a = pick(1)
if a {
    println("a {a}")
} else {
    println("a null")
}
let b = pick(9)
if b {
    println("b {b}")
} else {
    println("b null")
}
