// A `-> infer!` body may forward another callable's Result as its only error
// source: the Err type is inferred from the forwarded callee (a concrete
// constructor, or a generic one instantiated by the call's argument).
fun fixed_error() -> infer! {
    return Result.Err { error: "boom" }
}

fun wrap_error(value) -> infer! {
    return Result.Err { error: value }
}

fun forward_fixed(flag: bool) -> infer! {
    if flag {
        return 1
    }
    return fixed_error()
}

fun forward_generic(flag: bool) -> infer! {
    if flag {
        return 2
    }
    return wrap_error("bad")
}

println(forward_fixed(true))
println(forward_fixed(false))
println(forward_generic(true))
println(forward_generic(false))
