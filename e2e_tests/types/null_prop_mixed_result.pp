// A body mixing bare returns, `error(...)` propagation, and a nullable `!`
// infers `Result<int32, string>?`: the fallible Result from the error sites,
// wrapped nullable by the null propagation. Consume by narrowing the outer
// `?` first, then matching the Result.
fun f(c: int32) {
    if c == 0 {
        return 1
    } else if c == 1 {
        error("a")!
    } else {
        null!
    }
}

fun show(c: int32) {
    let r = f(c)
    if r {
        match r {
            Ok { value } => println("ok {value}"),
            Err { error } => println("err {error}"),
        }
    } else {
        println("null")
    }
}

show(0)
show(1)
show(2)
