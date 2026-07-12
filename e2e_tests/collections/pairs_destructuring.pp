// A `for` loop variable is a PATTERN, not just a name, so each element
// destructures in the loop header. `HashMap.pairs()` yields `[key, value]`
// tuples, which is what makes `for [k, v] in m.pairs()` read the way it does.
//
// Two things had to hold. The parser only accepted an identifier there, so the
// destructuring form was a syntax error. And a tuple pattern's match test is a
// length check, which the JIT answered by reading an array's length field -- a
// tuple has none, so a `match` over one never matched, while the interpreter
// (which reads the value's own length) always did. The two back ends disagreed.

import std.collections.{ HashMap }

fun main() {
    // Over an array of tuples, in a deterministic order.
    const ps = [["a", 1], ["b", 2], ["c", 3]]
    let sum: int64 = 0
    for [key, value] in ps {
        println("{key} = {value}")
        sum += value
    }
    println(sum)

    // Over a map's pairs. The map's own order is its slot order, so total rather
    // than the sequence is what this pins.
    let m: HashMap { key: string, value: int64 } = HashMap.new()
    m.set("x", 10)
    m.set("y", 32)
    let total: int64 = 0
    for [key, value] in m.pairs() {
        total += value
    }
    println(total)

    // A plain loop variable still binds the whole element.
    for p in ps {
        println(p[0])
    }

    // The same pattern in a `let` and in a `match` arm.
    let [k, v] = ps[1]
    println("{k}/{v}")
    match ps[2] {
        [k2, v2] => { println("{k2}:{v2}") }
    }
}
