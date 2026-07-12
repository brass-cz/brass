// A record field declared with a `type Alias = Base { .. }` refinement must
// resolve to the alias's concrete instance. The name is not a nominal of its
// own, so leaving it to the nominal table left the field open: the program
// type-checked but the back end refused it ("unsupported type ... deps=?").
import std.collections.{ HashMap }

type Counts = HashMap { key: string, value: int64 }

type Report = {
    title: string
    counts: Counts
}

fun Report.build(title: string) -> Report {
    let counts: Counts = HashMap.new()
    counts.set("hits", 3)
    counts.set("misses", 1)
    return Report { title: title, counts: counts }
}

const r = Report.build("run")
println(r.title)
println(r.counts.get("hits"))
println(r.counts.size())

// The alias also names the field's type from another signature.
fun total(counts: Counts) -> int64 {
    let sum: int64 = 0
    for [_, v] in counts.pairs() {
        sum += v
    }
    return sum
}
println(total(r.counts))
