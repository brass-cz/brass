// Numeric conversions and limits. The `Type.from` / `Type.parse`
// forms are recognized directly by the runtime; these named wrappers and the
// constants complement them and are part of the prelude.

const INT32_MAX = 2147483647
const INT32_MIN = -2147483648
const INT64_MAX = 9223372036854775807

// The conversions that can fail return `T!` (a `Result`): the `!` propagates the
// underlying conversion's error, and the success value is wrapped as `Ok`.
fun int32_from(x) -> int32! {
    return int32.from(x)!
}

fun int32_parse(s: string) -> int32! {
    return int32.parse(s)!
}

fun float64_from(x) -> float64 {
    return float64.from(x)
}

fun float64_parse(s: string) -> float64! {
    return float64.parse(s)!
}

fun string_from(x) -> string {
    return string.from(x)
}
