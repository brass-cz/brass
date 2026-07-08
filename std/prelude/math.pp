// Standard numeric helpers. `min`/`max`/`abs` are polymorphic over any type
// supporting `<`/`-`; the float routines wrap runtime primitives. Part of the
// implicit prelude.

/** The absolute value of `x`, for any numeric type. */
// `x - x` yields a correctly typed zero so this works for any numeric type
// without a typed literal.
fun abs(x) {
    let zero = x - x
    if x < zero {
        return zero - x
    }
    return x
}

/** The smaller of `a` and `b`, ordered with `<`. */
fun min(a, b) {
    if a < b {
        return a
    }
    return b
}

/** The larger of `a` and `b`, ordered with `>`. */
fun max(a, b) {
    if a > b {
        return a
    }
    return b
}

/** The square root of `x`. */
fun sqrt(x) -> float64 {
    return _float_sqrt(x)
}

/** The largest whole number not greater than `x`. */
fun floor(x) -> float64 {
    return _float_floor(x)
}

/** The smallest whole number not less than `x`. */
fun ceil(x) -> float64 {
    return _float_ceil(x)
}

/** `base` raised to the power `exp`. */
fun pow(base, exp) -> float64 {
    return _float_pow(base, exp)
}
