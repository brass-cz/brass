// An UNANNOTATED, FALLIBLE function that reads one map and builds a DIFFERENT one:
// the input's value type (a record) is not the output's (a string).
//
// A propagating body's return is assembled by the light pass -- only it builds the
// `Result` wrapping -- but its Ok PAYLOAD is the full check's, and the two are tied
// together so the map the body fills does not reach the back end with its element
// types unset. Reconciling the body's returns for that payload has to DROP the
// `error(..)` ones: their payload is a variable no path produces, and left in they
// win, the payload stays open, and the caller's `out.pairs()` monomorphizes at a
// map whose value type is not the one the body stores (a segfault, not a refusal).
import std.collections.{ HashMap }

type Dep = {
    name: string
}
type Deps = HashMap { key: string, value: Dep }

fun resolve(deps: Deps) {
    let result = HashMap.new()
    for [key, val] in deps.pairs() {
        if len(key) == 0 {
            return error("empty key")
        }
        result.set(val.name, "path/{val.name}")
    }
    return result
}

fun main() {
    let deps: Deps = HashMap.new()
    deps.set("a", Dep { name: "alpha" })
    const out = resolve(deps)!
    for [k, v] in out.pairs() {
        println("{k} -> {v}")
    }
}
