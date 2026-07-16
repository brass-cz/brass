type MyResult: Result =
    | Ok {
        value: int32
        message: string
    }
    | Err {
        error: string
    }

fun mk(flag: bool) -> MyResult {
    if flag {
        return MyResult.Ok { value: 20, message: "made" }
    }
    return MyResult.Err { error: "denied" }
}

fun f(flag: bool) -> int32! {
    let v = mk(flag)!
    return v + 1
}

println(f(true))
println(f(false))
