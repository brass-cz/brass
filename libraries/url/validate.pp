// Validation of a single URI component against its RFC 3986 character class.

import charset.{ is_hex_digit, is_userinfo_char, is_reg_name_char, is_path_char, is_query_char, is_ip_literal_char }

/** The character class a component is checked against. */
type CharClass =
    | Userinfo
    | RegName
    | IpLiteral
    | Path
    | Query
    | Fragment

fun CharClass.name(self) -> string {
    return match self {
        Userinfo => "userinfo",
        RegName => "host",
        IpLiteral => "IP literal",
        Path => "path",
        Query => "query",
        Fragment => "fragment",
    }
}

/** Whether `c` may appear literally, i.e. without percent-encoding. */
fun CharClass.allows(self, c: string) -> bool {
    return match self {
        Userinfo => is_userinfo_char(c),
        RegName => is_reg_name_char(c),
        IpLiteral => is_ip_literal_char(c),
        Path => is_path_char(c),
        Query => is_query_char(c),
        Fragment => is_query_char(c),
    }
}

/**
 * Checks that `s` only holds characters `kind` allows, plus well-formed `%XX`
 * escapes. An IP literal admits no escapes at all. Returns `s` unchanged, so a
 * caller can validate a component as it binds it.
 */
fun validate(s: string, kind: CharClass) -> string! {
    let cs = s.chars()
    let n = len(cs)
    let i: int64 = 0
    while i < n {
        let c = cs[i]
        if c == "%" {
            if let IpLiteral = kind {
                return error("percent-encoding is not allowed in an IP literal")
            }
            if i + 2 >= n { return error("truncated percent escape in {kind.name()}: {s}") }
            if !is_hex_digit(cs[i + 1]) || !is_hex_digit(cs[i + 2]) {
                return error("invalid percent escape in {kind.name()}: {s}")
            }
            i += 3
            continue
        }
        if !kind.allows(c) {
            return error("character `{c}` is not allowed in {kind.name()}: {s}")
        }
        i += 1
    }
    return s
}
