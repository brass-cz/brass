type Rich = {
    msg: string
    frames: int32[]
}

fun describe(e) -> string {
    if e.frames {
        return "rich"
    }
    return "plain"
}

println(describe(Rich { msg: "a", frames: [] }))
println(describe("bare"))
println(describe(7))
