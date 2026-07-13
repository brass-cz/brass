// An `if`/`match` branch that DIVERGES (`error(..)!`, which propagates or aborts)
// produces a value nothing constrains: the Ok payload of the `error(..)` is a
// fresh variable no path ever builds. Joining the branches only PROBED that the
// two types could unify, so that variable stayed open, and the back end -- which
// defaults an unresolved local to `void` -- had the branch assign a void into the
// expression's rc-managed slot: `pp_retain(i1 false)`, rejected by the LLVM
// verifier. Both branches of one `if` yield one type, so the join binds them.
type Report = {
    status: int32
}

fun fetch(ok: bool) -> Report! {
    if !ok {
        return error("no report")
    }
    return Report { status: 200 }
}

fun body(ok: bool) -> string! {
    if !ok {
        return error("no body")
    }
    return "text"
}

fun main() {
    // if-let over a Result, diverging else.
    const r = if let Ok { value } = fetch(true) {
        value
    } else {
        error("unreachable")!
    }
    println(r.status)

    // Nested, with a heap payload on the inner one too.
    const b = if let Ok { value } = fetch(true) {
        if let Ok { value } = body(value.status == 200) {
            value
        } else {
            error("unreachable")!
        }
    } else {
        error("unreachable")!
    }
    println(b)

    // A plain `if` whose else diverges.
    const flag = true
    const r2 = if flag {
        Report { status: 1 }
    } else {
        error("unreachable")!
    }
    println(r2.status)

    // A `match` arm that diverges.
    const r3 = match fetch(true) {
        Ok { value } => value,
        Err { error } => error("unreachable: {error}")!,
    }
    println(r3.status)
}
