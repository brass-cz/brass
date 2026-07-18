// Type tests for the primitive classes. Each primitive type implements only
// its own `is_<type>` method, so the MEMBER-PRESENCE test (see the book's
// reflection reference) answers the question at compile time: `v.is_string`
// is truthy exactly when `v` is a `string`, and reads as `null` on every
// other type. That makes `if v.is_string { ... } else ... ` a per-type
// dispatch inside one generic body. Calling the method (`v.is_string()`)
// always returns `true` -- it is only reachable on the matching type.

fun string.is_string(self) -> bool {
    return true
}

fun bool.is_bool(self) -> bool {
    return true
}

fun int8.is_int8(self) -> bool {
    return true
}

fun int16.is_int16(self) -> bool {
    return true
}

fun int32.is_int32(self) -> bool {
    return true
}

fun int64.is_int64(self) -> bool {
    return true
}

fun uint8.is_uint8(self) -> bool {
    return true
}

fun uint16.is_uint16(self) -> bool {
    return true
}

fun uint32.is_uint32(self) -> bool {
    return true
}

fun uint64.is_uint64(self) -> bool {
    return true
}

fun float32.is_float32(self) -> bool {
    return true
}

fun float64.is_float64(self) -> bool {
    return true
}

fun infer[].is_array(self) -> bool {
    return true
}
