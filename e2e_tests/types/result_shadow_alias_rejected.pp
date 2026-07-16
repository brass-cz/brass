// An alias named `Result` cannot carry the fallibility sugar's identity; the
// sugar needs a sum declared with the name `Result`.
type Two =
    | Ok {
        value
    }
    | Err {
        error
    }
type Result = Two

fun f() -> int32! {
    return error("boom")
}

println(f())
