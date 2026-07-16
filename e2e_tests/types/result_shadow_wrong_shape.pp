// A shadowing `type Result` must have the `| Ok { value } | Err { error }`
// shape the fallibility sugar builds.
type Result =
    | Yes {
        v
    }
    | No {
        e
    }

fun f() -> int32! {
    return error("boom")
}

println(f())
