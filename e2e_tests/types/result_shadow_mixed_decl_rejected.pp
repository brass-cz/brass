// `!` propagates its operand's Result unchanged, so an operand carrying the
// prelude's Result (a builtin's return) cannot propagate out of a function
// whose return type is the module's shadowing Result.
type Result =
    | Ok {
        value
    }
    | Err {
        error: string
    }

fun f() -> int32! {
    let x = int32.parse("3")!
    return x
}

println(f())
