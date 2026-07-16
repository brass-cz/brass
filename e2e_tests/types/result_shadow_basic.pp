// A module-local `type Result` shadows the prelude's for the fallibility
// sugar: `T!`, `error(..)`, Ok-wrapping, and `!` all build/unwrap the shadow.
// Its annotated Err payload pins the sugar's error type to string.
type Result =
    | Ok {
        value
    }
    | Err {
        error: string
    }

fun parse(x: int32) -> int32! {
    if x < 0 {
        // `error(..)` is the prelude's and builds the prelude's Result; a
        // shadowing module constructs its own Result directly.
        return Result.Err { error: "negative" }
    }
    return x * 2
}

fun run(x: int32) -> string {
    return match parse(x) {
        Ok { value } => "ok {value}"
        Err { error } => "err {error}"
    }
}

println(run(5))
println(run(-1))
let unwrapped = parse(21)!
println(unwrapped)
