// A refinement alias `type Alias = Base { slot: T, .. }` pins a slotted record's
// type parameters, naming a concrete instance. `Counts` is a fully concrete
// `string -> int64` box; a value built by the witness-free constructor unifies
// with the refined type, so it may be passed where `Counts` is annotated.

type _Entry = {
    key
    value
}

type Box = {
    key: type
    value: type
    slots_arr: _Entry { key: Self.key, value: Self.value }?[]
    count: int64
}

type Counts = Box {
    key: string,
    value: int64,
}

fun Box.new() {
    let arr = []
    let i: int64 = 0
    while i < 4 {
        arr.push(null)
        i += 1
    }
    return Self { slots_arr: arr, count: 0 }
}

fun Box.put(self, idx, k, v) {
    self.slots_arr[idx] = _Entry { key: k, value: v }
    self.count += 1
}

// Annotated with the refined concrete type.
fun sum_values(c: Counts) -> int64 {
    let total: int64 = 0
    for slot in c.slots_arr {
        if let e = slot {
            total += e.value
        }
    }
    return total
}

fun main() {
    let b = Box.new()
    b.put(0, "a", 10)
    b.put(1, "b", 32)
    println(sum_values(b))
    println(b.count)
}
