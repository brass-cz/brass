// Type slots (`key`/`value: type`): a record's type parameters with no runtime
// storage. `slots_arr` expresses its element type over them via `Self.key` /
// `Self.value`, so storing an `_Entry` pins the key/value types. The container
// stays witness-free -- `Box.new()` takes no arguments and no sample values --
// and the slots never appear in the layout, in `fields()`, or in construction.

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

fun Box.value_at(self, idx) {
    if let e = self.slots_arr[idx] {
        return e.value
    }
    return null
}

fun main() {
    let b = Box.new()
    b.put(0, "a", 10)
    b.put(1, "b", 20)
    println(b.value_at(0))
    println(b.value_at(1))
    println(b.count)
    // Slots are not value fields: `fields()` sees only the real fields.
    for f in fields(b) {
        println(f)
    }
}
