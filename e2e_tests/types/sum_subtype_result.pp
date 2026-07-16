type MyResult: Result =
    | Ok {
        value: int32
        message: string
    }
    | Err {
        error: string
    }

fun a() -> int32! {
    return MyResult.Err { error: "message" }
}

fun b(flag: bool) -> int32! {
    if flag {
        return 7
    }
    return MyResult.Err { error: "bad flag" }
}

fun c(flag: bool) -> MyResult {
    if flag {
        return MyResult.Ok { value: 3, message: "made" }
    }
    return MyResult.Err { error: "no" }
}

println(a())
println(b(true))
println(b(false))
fun let_coerce() {
    let via: int32! = MyResult.Err { error: "direct" }
    println(via)
}
let_coerce()
println(match c(true) {
    Ok { value, message } => "{message}: {value}"
    Err { error } => "err {error}"
})
println(b(true)!)
