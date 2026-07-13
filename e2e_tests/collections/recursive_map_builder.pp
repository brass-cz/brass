// A recursive, UNANNOTATED function that builds a witness-free container and
// merges its own recursive result back into it.
//
// The recursive call can only read the PRECOMPUTED (light-pass) return -- the real
// one is what checking the body produces -- and the light pass gets a constructor's
// result wrong: it infers `HashMap.new()`'s body without the type's scheme, so the
// map it hands back has the fields that body could see (`_entries: never?[]`, a slot
// array sized with `null`) rather than the ones the scheme expresses over the type's
// parameters. The element types then had nowhere to be pinned, `collect(..)!.pairs()`
// monomorphized at an open type, and the typed back end refused a program `check`
// had accepted.
import std.collections.{ HashMap }

fun collect(names: string[]) {
    let result = HashMap.new()
    for n in names {
        result.set(n, n.len())
        // Merge what the recursion found. `names` shrinks, so this terminates.
        if len(names) > 1 {
            for [k, v] in collect([names[0]])!.pairs() {
                result.set(k, v)
            }
        }
    }
    if len(names) > 100 {
        return error("too many names")
    }
    return result
}

// A bare nominal annotation leaves the map's key/value to the call site.
fun render(m: HashMap) {
    // Slot order is unspecified, so the keys are looked up in a fixed order.
    let out: string[] = []
    for k in ["a", "bb", "ccc"] {
        if let v = m.get(k) {
            out.push("{k}={v}")
        }
    }
    return out.join(",")
}

fun main() {
    println(render(collect(["a", "bb", "ccc"])!))
}
