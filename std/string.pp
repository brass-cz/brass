// Standard string utilities built on the `_string_*` runtime primitives.
// All string indices are UTF-8 byte offsets: `len`, slicing, `find`, indexing,
// and `_string_char_at` agree on byte positions, and the per-character helpers
// advance by each character's byte length. Part of the implicit prelude.

// Split `s` on every occurrence of `sep`.
fun split(s: string, sep: string) -> string[] {
    let result = []
    // An empty separator has a match at every position, so `_string_find` always
    // returns 0 and `start` never advances -- an infinite loop. Treat it as no
    // split (the whole string), mirroring `replace`'s empty-`old` guard.
    if len(sep) == 0 {
        result.push(s)
        return result
    }
    let start: int64 = 0
    while start < len(s) {
        let rest = _string_slice(s, start, len(s))
        let pos = _string_find(rest, sep)
        if pos != null {
            result.push(_string_slice(s, start, start + pos))
            start = start + pos + len(sep)
        } else {
            result.push(_string_slice(s, start, len(s)))
            start = len(s)
        }
    }
    if len(s) == 0 {
        result.push("")
    }
    return result
}

// Strip leading and trailing ASCII whitespace.
fun trim(s: string) -> string {
    let one: int64 = 1
    let start: int64 = 0
    let end = len(s)
    while start < end {
        let c = _string_char_at(s, start)
        if c == " " || c == "\t" || c == "\n" || c == "\r" {
            start += one
        } else {
            break
        }
    }
    while end > start {
        let c = _string_char_at(s, end - one)
        if c == " " || c == "\t" || c == "\n" || c == "\r" {
            end -= one
        } else {
            break
        }
    }
    return _string_slice(s, start, end)
}

fun starts_with(s: string, prefix: string) -> bool {
    if len(prefix) > len(s) {
        return false
    }
    return _string_slice(s, 0, len(prefix)) == prefix
}

fun ends_with(s: string, suffix: string) -> bool {
    if len(suffix) > len(s) {
        return false
    }
    return _string_slice(s, len(s) - len(suffix), len(s)) == suffix
}

// `s.find(sub)`: the byte offset of the first occurrence of substring `sub` in
// `s`, or null if absent. This is the string substring search, distinct from the
// polymorphic element-membership `contains` (use `s.find(sub) != null` for a
// substring test).
fun find(s: string, sub: string) -> int64? {
    return _string_find(s, sub)
}

// Replace every occurrence of `old` with `new`.
fun replace(s: string, old: string, new: string) -> string {
    if len(old) == 0 {
        return s
    }
    let result = ""
    let start: int64 = 0
    while start < len(s) {
        let rest = _string_slice(s, start, len(s))
        let pos = _string_find(rest, old)
        if pos != null {
            result = result + _string_slice(s, start, start + pos) + new
            start = start + pos + len(old)
        } else {
            result = result + _string_slice(s, start, len(s))
            start = len(s)
        }
    }
    return result
}

// The characters of `s` as a one-element-per-character array. Advances by each
// character's byte length so multibyte UTF-8 characters are handled correctly.
fun chars(s: string) -> string[] {
    let result = []
    let i: int64 = 0
    while i < len(s) {
        if let c = _string_char_at(s, i) {
            result.push(c)
            i += len(c)
        } else {
            break
        }
    }
    return result
}

// Join `parts` with `sep` between each.
fun join(parts: string[], sep: string) -> string {
    let result = ""
    let first = true
    for p in parts {
        if first {
            result = result + p
            first = false
        } else {
            result = result + sep + p
        }
    }
    return result
}

// ASCII upper-casing implemented over the UTF-8 byte view. An ASCII case change
// preserves UTF-8 validity, so the byte->string conversion cannot fail; matching
// (rather than `!`) keeps `to_upper` non-fallible, returning `string` not `string!`.
fun to_upper(s: string) -> string {
    let bytes = _string_bytes(s)
    let result = []
    for b in bytes {
        if b >= 97 && b <= 122 {
            result.push(b - 32)
        } else {
            result.push(b)
        }
    }
    return match _string_from_bytes(result) {
        Ok { value } => value,
        Err { error } => s,
    }
}

fun to_lower(s: string) -> string {
    let bytes = _string_bytes(s)
    let result = []
    for b in bytes {
        if b >= 65 && b <= 90 {
            result.push(b + 32)
        } else {
            result.push(b)
        }
    }
    return match _string_from_bytes(result) {
        Ok { value } => value,
        Err { error } => s,
    }
}
