// Matching a narrowed nullable SUM dispatches on the actual variant: the
// scrutinee local still carries `S?`, so the tag test must unwrap the
// nullable before comparing (previously the `B` value below matched the `A`
// arm on the typed back end and read a garbage field).
type S = | A { x: int32 } | B

fun m(c: int32) -> S? {
    if c == 0 {
        return S.A { x: 5 }
    }
    if c == 1 {
        return S.B
    }
    return null
}

fun show(c: int32) {
    let r = m(c)
    if r {
        match r {
            A { x } => println("a {x}"),
            B => println("b"),
        }
    } else {
        println("none")
    }
}

show(0)
show(1)
show(2)
