// Assertions. Part of the prelude.

/**
 * Abort the program if `cond` is false. The message is optional: `msg` is a
 * trailing nullable parameter, so callers may write `assert(cond)` (msg
 * defaults to null, using the generic text) or `assert(cond, "detail")`.
 */
fun assert(cond: bool, msg: string?) {
    if !cond {
        if msg {
            _panic(msg)
        } else {
            _panic("assertion failed")
        }
    }
}
