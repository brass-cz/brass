type Result =
    | Ok {
        value
    }
    | Err {
        error: string
    }

fun f() -> int32! {
    return error("boom")
}

fun g() {
    // The module's shadowing Result and the prelude's must not unify: a
    // builtin's std Result cannot initialize a shadow-typed binding.
    let x: int32! = int32.parse("3")
    println(x)
}

g()
