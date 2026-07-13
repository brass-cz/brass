// `T!` names only the OK payload: the error type is INFERRED, from the body's
// `error(..)` sites and the errors it forwards. A body whose ONLY propagation is
// its own recursive `!` forwards the very variable being inferred, so there is
// nothing to infer it from. Left open, it reached the back end, which has no type
// to lay the payload out at ("cannot infer the type of an expression temporary").
//
// (A `T!` that raises NO error at all is fine and stays so: its returns Ok-wrap
// and nothing ever reads the Err -- see `structure/fallible_open`.)
import std.collections.{ HashMap }

type M = HashMap { key: string, value: int64 }

fun collect(names: string[]) -> M! {
    let result: M = HashMap.new()
    for n in names {
        result.set(n, n.len())
        if n == "seed" {
            for [k, v] in collect([])!.pairs() {
                result.set(k, v)
            }
        }
    }
    return result
}

fun main() {
    println(collect(["a"])!.get("a"))
}
