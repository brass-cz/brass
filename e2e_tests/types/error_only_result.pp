// A Result no context constrains still types: an `error(..)` printed
// directly, and an Err-only body, default the uninhabited Ok payload.
type MyResult: Result =
    | Ok {
        value
        message
    }
    | Err {
        error
    }

fun a() -> infer! {
    return MyResult.Err { error: "message" }
}

println(error("boom"))
println(a())
