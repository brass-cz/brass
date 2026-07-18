// Numeric conversions and limits. The `Type.from` / `Type.parse`
// forms are recognized directly by the runtime; these named wrappers and the
// constants complement them and are part of the prelude.

const INT32_MAX = 2147483647
const INT32_MIN = -2147483648
const INT64_MAX = 9223372036854775807
// The literal -9223372036854775808 cannot be written directly (the magnitude
// alone overflows int64 before the minus applies), so the minimum is built
// arithmetically.
const INT64_MIN = -9223372036854775807 - 1

// The conversions that can fail return `T!` (a `Result`): the `!` propagates the
// underlying conversion's error, and the success value is wrapped as `Ok`.

/** Convert a numeric value to `int32`. Fails when the value does not fit. */
fun int32_from(x) -> int32! {
    return int32.from(x)!
}

/** Parse a decimal string as `int32`. Fails on malformed or out-of-range input. */
fun int32_parse(s: string) -> int32! {
    return int32.parse(s)!
}

/** Convert a numeric value to `float64`. */
fun float64_from(x) -> float64 {
    return float64.from(x)
}

/** Parse a decimal string as `float64`. Fails on malformed input. */
fun float64_parse(s: string) -> float64! {
    return float64.parse(s)!
}

/** The text rendering of any value, as `print` would show it. */
fun string_from(x) -> string {
    return string.from(x)
}

/** The UTF-8 bytes of `s`, ready to `write`/`send_to`. */
fun to_bytes(s: string) -> uint8[] {
    return _string_bytes(s)
}

/** Decode bytes as UTF-8 text. Fails on invalid UTF-8. */
fun to_text(bytes: uint8[]) -> string! {
    return _string_from_bytes(bytes)!
}
