// Key/value pairs of a query string, in the `application/x-www-form-urlencoded`
// reading of it: `&` separates pairs, the first `=` separates key from value,
// and `+` stands for a space. RFC 3986 itself gives the query no structure, so
// this convention is a layer above it.

import text.{ substr, index_of }
import percent

type QueryPair = {
    key: string
    value: string
}

/**
 * Splits a query string into decoded pairs. A pair with no `=` yields an empty
 * value; empty segments (`a=1&&b=2`) are skipped. Fails when a percent escape
 * is malformed.
 */
fun QueryPair.parse_all(q: string) -> QueryPair[]! {
    let out: QueryPair[] = []
    for item in q.split("&") {
        if len(item) == 0 { continue }
        let cs = item.chars()
        let n = len(cs)
        let eq = index_of(cs, "=", 0, n)
        let key = item
        let value = ""
        if eq {
            key = substr(cs, 0, eq)
            value = substr(cs, eq + 1, n)
        }
        out.push(Self {
            key: _decode_form(key)!,
            value: _decode_form(value)!,
        })
    }
    return out
}

/** Re-encodes pairs into a query string. A space becomes `%20`, not `+`. */
fun QueryPair.format_all(pairs: QueryPair[]) -> string {
    let parts: string[] = []
    for p in pairs {
        parts.push("{percent.encode_component(p.key)}={percent.encode_component(p.value)}")
    }
    return parts.join("&")
}

// `+` is replaced before decoding, so a literal plus written as %2B survives.
fun _decode_form(s: string) -> string! {
    return percent.decode(s.replace("+", " "))!
}
