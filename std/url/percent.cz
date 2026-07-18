// Percent-encoding (RFC 3986 section 2.1).

import charset.{ hex_value, is_unreserved }

const _HEX_UPPER = "0123456789ABCDEF".chars()

fun _hex_byte(b: uint8) -> string {
    let v: int32 = b
    return "%{_HEX_UPPER[v >> 4]}{_HEX_UPPER[v & 15]}"
}

/** The byte the hex digits `hi` and `lo` spell. */
fun _hex_pair(hi: string, lo: string) -> uint8! {
    let h = hex_value(hi)
    if h {
        let l = hex_value(lo)
        if l {
            let b: int64 = h * 16 + l
            return uint8.from(b)!
        }
    }
    return error("invalid percent escape `%{hi}{lo}`")
}

/**
 * Percent-decodes `s`, resolving every `%XX` triplet.
 *
 * Fails on a truncated or non-hex escape, and when the decoded bytes do not
 * form valid UTF-8 (a lone `%FF`, say).
 */
fun decode(s: string) -> string! {
    let cs = s.chars()
    let n = len(cs)
    let out: uint8[] = []
    let i: int64 = 0
    while i < n {
        let c = cs[i]
        if c == "%" {
            if i + 2 >= n { return error("truncated percent escape at offset {i}") }
            out.push(_hex_pair(cs[i + 1], cs[i + 2])!)
            i += 3
            continue
        }
        for b in to_bytes(c) { out.push(b) }
        i += 1
    }
    return to_text(out)!
}

/**
 * Percent-encodes `s`. Unreserved characters and the ASCII characters listed in
 * `extra` are kept as they are; every other byte becomes an uppercase `%XX`
 * triplet.
 */
fun encode(s: string, extra: string) -> string {
    let out = ""
    for c in s.chars() {
        // A one-byte character is ASCII, the only kind either set can hold.
        if len(c) == 1 && (is_unreserved(c) || extra.find(c) != null) {
            out += c
            continue
        }
        for b in to_bytes(c) { out += _hex_byte(b) }
    }
    return out
}

/** Percent-encodes everything outside the unreserved set. */
fun encode_component(s: string) -> string {
    return encode(s, "")
}
