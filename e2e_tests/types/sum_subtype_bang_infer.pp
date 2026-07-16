type Lookup: Result =
    | Ok {
        value: int32
        source: string
    }
    | Err {
        error: string
    }

fun find_port(name: string) -> Lookup {
    if name == "http" {
        return Lookup.Ok { value: 80, source: "well-known" }
    }
    return Lookup.Err { error: "unknown service `{name}`" }
}

// The `!` on a declared Result subtype must not define this callable's Ok
// payload from the SUBTYPE's (int32): the inferred Ok is the string the body
// returns, and the propagated payload lifts into the prelude Error like a
// plain Result's.
fun connect(name: string) -> infer! {
    let port = find_port(name)!
    return "{name}:{port}"
}

fun main() {
    println(connect("http")!)
    match connect("gopher") {
        Ok { value } => { println(value) }
        Err { error } => { println("failed: {error.value}") }
    }
}
