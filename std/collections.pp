// A hash map with open-addressing (linear-probing) storage, written in Prepoly on
// the runtime string/array primitives. Keys may be of any type that renders to a
// stable string and compares with `==` (integers, strings, records, ...); values
// may be of any type. Part of the standard library. The table's operations are
// implemented as methods with `fun HashMap.m(...)` in this same module.
//
// `HashMap.new()` takes no arguments. Open addressing stores at a computed slot
// index (`entries[idx] = ..`) rather than appending, so the slot array must be
// allocated up front; it is pre-filled with `null`, which sizes it without
// needing a sample value. The key/value types are inferred from the first
// `set`/`from_pairs`: the slot element is a nullable `_Entry?`, and storing a
// concrete `_Entry` fixes its key/value types (the back end follows the resolved
// instance). So `let m = HashMap.new()` followed by `m.set("a", 1)` is a
// `string -> int32` map with no type annotations or witness values.

// One stored key/value pair. Private to this module: it is an implementation
// detail of the table's slot array, not part of the public surface.
type _Entry = {
    key
    value
}

/**
 * A hash map from keys to values. Keys may be of any type that renders to a
 * stable string and compares with `==` (integers, strings, records, ...);
 * values may be of any type. Construct with `HashMap.new()` or
 * `HashMap.from_pairs(...)`; the key/value types are inferred from the first
 * stored pair, or pinned by a refinement such as
 * `type StringCount = HashMap { key: string, value: int32 }`.
 */
type HashMap = {
    // `key`/`value` are type SLOTS -- the map's key and value types -- declared
    // with the `type` marker. They have no runtime storage; they name the type
    // parameters the fields below are expressed over. A refinement pins them,
    // so `type StringCount = HashMap { key: string, value: int32 }` is a fully
    // concrete instance, and a bare `HashMap.new()` leaves them to inference.
    key: type
    value: type
    // Slot arrays, parallel and `cap`-long. `entries[i]` is meaningful only when
    // `states[i]` is `_FULL`. A slot is `_EMPTY` (never used), `_FULL` (holds a
    // live pair), or `_TOMB` (deleted -- probing passes through it, insertion may
    // reuse it). `entries` is a nullable-element array of `_Entry` whose key/value
    // types are the slots (`Self.key`/`Self.value`): empty slots hold `null`,
    // which sizes the array at construction without a sample value, and storing a
    // concrete `_Entry` fixes the slots (the back end follows the resolved
    // instance).
    entries: _Entry { key: Self.key, value: Self.value }?[]
    _states: int32[]
    // `cap` is the slot count (a power of two is not required; the table grows by
    // doubling). `count` is the number of live pairs; `tombs` the number of
    // tombstones. The table grows when `count + tombs` reaches 3/4 of `cap`, which
    // keeps an empty slot present so every probe terminates.
    cap: int64
    count: int64
    tombs: int64
}

/** An empty map. The key/value types are inferred from the values stored later. */
// The slot array is sized with `null` (see the module comment).
fun HashMap.new() {
    let cap: int64 = 8
    let zero: int64 = 0
    let entries = []
    let states = []
    let i: int64 = 0
    while i < cap {
        entries.push(null)
        states.push(0)
        i += 1
    }
    return Self { entries: entries, _states: states, cap: cap, count: zero, tombs: zero }
}

/** A map built from an array of `[key, value]` pairs. */
fun HashMap.from_pairs(pairs) {
    let m = Self.new()
    for p in pairs {
        m.set(p[0], p[1])
    }
    return m
}

// The home slot for `key`: an FNV-style polynomial hash over the bytes of the
// key's string rendering, reduced into `[0, cap)`. `string.from` renders any
// value, so the table is key-type agnostic; the per-byte modulus keeps the
// accumulator in a non-negative 31-bit range, so the final index is in range.
fun HashMap._hash(self, key) -> int64 {
    let bytes = _string_bytes(string.from(key))
    let h: int64 = 2166136261
    for b in bytes {
        h = (h * 16777619 + b) % 2147483647
    }
    return h % self.cap
}

// The index of `key` if present, else -1. Linear probing stops at the first
// `_EMPTY` slot: under this scheme a present key always sits before the first
// empty slot in its probe sequence, so an empty slot proves absence.
fun HashMap._find(self, key) -> int64 {
    let one: int64 = 1
    let absent = 0 - one
    let h = self._hash(key)
    let step: int64 = 0
    while step < self.cap {
        let idx = (h + step) % self.cap
        let s = self._states[idx]
        if s == 0 {
            return absent
        }
        if s == 1 {
            if let e = self.entries[idx] {
                if e.key == key {
                    return idx
                }
            }
        }
        step += 1
    }
    return absent
}

// Place `key`/`value` into the first non-`_FULL` slot of `key`'s probe
// sequence. The caller guarantees `key` is absent and a free slot exists (the
// load factor keeps one), so this only inserts -- it never updates. Reusing a
// tombstone reclaims it.
fun HashMap._insert(self, key, value) {
    let one: int64 = 1
    let h = self._hash(key)
    let step: int64 = 0
    while step < self.cap {
        let idx = (h + step) % self.cap
        if self._states[idx] != 1 {
            if self._states[idx] == 2 {
                self.tombs -= one
            }
            self.entries[idx] = _Entry { key: key, value: value }
            self._states[idx] = 1
            self.count += one
            return
        }
        step += 1
    }
}

// Rehash every live pair into a fresh `new_cap`-slot table, dropping tombstones.
// The new slot array is sized with `null`, like `new`.
fun HashMap._grow(self, new_cap) {
    let zero: int64 = 0
    let old_entries = self.entries
    let old_states = self._states
    let old_cap = self.cap
    let entries = []
    let states = []
    let i: int64 = 0
    while i < new_cap {
        entries.push(null)
        states.push(0)
        i += 1
    }
    self.entries = entries
    self._states = states
    self.cap = new_cap
    self.count = zero
    self.tombs = zero
    let j: int64 = 0
    while j < old_cap {
        if old_states[j] == 1 {
            if let e = old_entries[j] {
                self._insert(e.key, e.value)
            }
        }
        j += 1
    }
}

/** Insert `key`/`value`, or overwrite the value if `key` is already present. */
// `self` is mutated (it stores into the slot arrays), so it is inferred as a
// mutable reference `ref(mut(Self))` -- like every other mutating method here.
fun HashMap.set(self, key, value) {
    let existing = self._find(key)
    if existing >= 0 {
        // Overwrite by replacing the whole slot: the element is a nullable
        // `_Entry?`, so its `value` field cannot be assigned through in place.
        if let e = self.entries[existing] {
            self.entries[existing] = _Entry { key: e.key, value: value }
        }
        return
    }
    // Grow before inserting a new key once the table is 3/4 full, so a free
    // slot always remains and probing terminates.
    if (self.count + self.tombs) * 4 >= self.cap * 3 {
        self._grow(self.cap * 2)
    }
    self._insert(key, value)
}

/** The value for `key`, or `null` if absent. */
fun HashMap.get(self, key) {
    let idx = self._find(key)
    if idx >= 0 {
        if let e = self.entries[idx] {
            return e.value
        }
    }
    return null
}

/**
 * The value for `key`, or `dflt` if absent. Unlike `get` this never returns
 * a nullable, so the result is usable without a null check.
 */
fun HashMap.get_or(self, key, dflt) {
    let idx = self._find(key)
    if idx >= 0 {
        if let e = self.entries[idx] {
            return e.value
        }
    }
    return dflt
}

/** Whether `key` is present. */
fun HashMap.contains_key(self, key) -> bool {
    return self._find(key) >= 0
}

/** Remove `key`, returning whether it was present. */
// The slot becomes a tombstone so probes for other keys still reach past it;
// tombstones are cleared on grow.
fun HashMap.delete(self, key) -> bool {
    let one: int64 = 1
    let idx = self._find(key)
    if idx < 0 {
        return false
    }
    self._states[idx] = 2
    self.tombs += one
    self.count -= one
    return true
}

/** The number of live pairs. */
fun HashMap.size(self) -> int64 {
    return self.count
}

/** Whether the map holds no pairs. */
fun HashMap.is_empty(self) -> bool {
    return self.count == 0
}

/** The live keys, in unspecified (slot) order. */
fun HashMap.keys(self) {
    let result = []
    let i: int64 = 0
    while i < self.cap {
        if self._states[i] == 1 {
            if let e = self.entries[i] {
                result.push(e.key)
            }
        }
        i += 1
    }
    return result
}

/** The live values, in the same order as `keys`. */
fun HashMap.values(self) {
    let result = []
    let i: int64 = 0
    while i < self.cap {
        if self._states[i] == 1 {
            if let e = self.entries[i] {
                result.push(e.value)
            }
        }
        i += 1
    }
    return result
}

/** The live pairs as `[key, value]` tuples, in the same order as `keys`. */
fun HashMap.pairs(self) {
    let result = []
    let i: int64 = 0
    while i < self.cap {
        if self._states[i] == 1 {
            if let e = self.entries[i] {
                result.push([e.key, e.value])
            }
        }
        i += 1
    }
    return result
}

/** Remove every pair, keeping the current capacity and key/value types. */
fun HashMap.clear(self) {
    let zero: int64 = 0
    let i: int64 = 0
    while i < self.cap {
        self._states[i] = 0
        i += 1
    }
    self.count = zero
    self.tombs = zero
}
