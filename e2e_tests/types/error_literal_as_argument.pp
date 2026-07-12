// A bare `error("..")` passed straight into a `T!` position must take that
// position's Ok payload.
//
// `error(..)` produces no Ok value, so nothing in the expression constrains its Ok
// payload -- only the position it flows into. Left open, the checker recorded it
// as `Result<?, string>`, which is not fully known, so it was never seeded onto
// the MIR local. The back end then types a bare `Result` CONSTRUCTION from the
// ENCLOSING callable's return type, so this typed the argument as `main`'s own
// `Result<void, string>`, instantiated the callee at that, and returned its `void`
// Ok payload from a function declared `int32`:
//
//     Function return type does not match operand type of return inst!
//       ret i1 false / i32
//
// Only the LLVM verifier caught it -- the REPL ran the same program fine, so the
// two back ends disagreed.

fun unwrap_or(r: int32!, dflt: int32) -> int32 {
    match r {
        Ok { value } => { return value }
        Err { error } => { return dflt }
    }
}

fun describe(r: string!) -> string {
    match r {
        Ok { value } => { return value }
        Err { error } => { return "err: {error}" }
    }
}

fun main() {
    // Directly as an argument, from a fallible `main` (whose own return type used
    // to be what typed these).
    println(unwrap_or(error("boom"), -1))
    println(describe(error("nope")))

    // The same value bound first still works (this path always did).
    const r: int32! = error("bound")
    println(unwrap_or(r, -2))

    // And a real Ok value takes the same instance.
    println(unwrap_or(ok_int(7), -3))
}

fun ok_int(n: int32) -> int32! {
    return n
}
