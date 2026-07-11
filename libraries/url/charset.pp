// Character classes of the RFC 3986 grammar. Every character that carries
// syntactic meaning in a URI is ASCII, so each predicate takes a one-character
// string and rejects anything it does not know.

const _DIGITS = "0123456789"
const _ALPHA = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
const _HEX_DIGITS = "0123456789abcdefABCDEF"
const _SUB_DELIMS = "!$&'()*+,;="
const _UNRESERVED_MARKS = "-._~"
const _SCHEME_MARKS = "+-."

// `find` on an empty needle reports a match at offset 0, so an empty `c` has to
// be rejected before the lookup.
fun _in_set(set: string, c: string) -> bool {
    if len(c) == 0 { return false }
    if set.find(c) { return true }
    return false
}

fun is_digit(c: string) -> bool {
    return _in_set(_DIGITS, c)
}

fun is_alpha(c: string) -> bool {
    return _in_set(_ALPHA, c)
}

fun is_hex_digit(c: string) -> bool {
    return _in_set(_HEX_DIGITS, c)
}

/** Numeric value 0..15 of a hex digit, or null when `c` is not one. */
fun hex_value(c: string) -> int64? {
    let i = _HEX_DIGITS.find(c)
    if !i { return null }
    // _HEX_DIGITS holds a-f at 10..15 and A-F at 16..21.
    if i < 16 { return i }
    return i - 6
}

fun is_sub_delim(c: string) -> bool {
    return _in_set(_SUB_DELIMS, c)
}

/** unreserved = ALPHA / DIGIT / "-" / "." / "_" / "~" */
fun is_unreserved(c: string) -> bool {
    if is_alpha(c) { return true }
    if is_digit(c) { return true }
    return _in_set(_UNRESERVED_MARKS, c)
}

/** A scheme starts with ALPHA and continues with ALPHA / DIGIT / "+" / "-" / "." */
fun is_scheme_char(c: string) -> bool {
    if is_alpha(c) { return true }
    if is_digit(c) { return true }
    return _in_set(_SCHEME_MARKS, c)
}

/** userinfo = *( unreserved / pct-encoded / sub-delims / ":" ) */
fun is_userinfo_char(c: string) -> bool {
    if is_unreserved(c) { return true }
    if is_sub_delim(c) { return true }
    return c == ":"
}

/** reg-name = *( unreserved / pct-encoded / sub-delims ) */
fun is_reg_name_char(c: string) -> bool {
    if is_unreserved(c) { return true }
    return is_sub_delim(c)
}

/** pchar = unreserved / pct-encoded / sub-delims / ":" / "@" */
fun is_pchar(c: string) -> bool {
    if is_userinfo_char(c) { return true }
    return c == "@"
}

/** path = *( pchar / "/" ) once pct-encoded triplets are taken out */
fun is_path_char(c: string) -> bool {
    if is_pchar(c) { return true }
    return c == "/"
}

/** query and fragment = *( pchar / "/" / "?" ) */
fun is_query_char(c: string) -> bool {
    if is_path_char(c) { return true }
    return c == "?"
}

/** The body of an IP-literal, i.e. the characters allowed between "[" and "]". */
fun is_ip_literal_char(c: string) -> bool {
    if is_hex_digit(c) { return true }
    if c == ":" { return true }
    if c == "." { return true }
    // IPvFuture keeps a few extra characters alive.
    if is_sub_delim(c) { return true }
    return c == "v"
}
