// Standard string utilities built on the `_string_*` runtime primitives, exposed
// as methods on `string` with `fun string.m`. All string indices are UTF-8 byte
// offsets: `len`, slicing, `find`, indexing, and `_string_char_at` agree on byte
// positions, and the per-character helpers advance by each character's byte
// length. Part of the implicit prelude.

/**
 * Split `self` on every occurrence of `sep`, one field per boundary: interior
 * and trailing empty fields are kept, and an empty `sep` yields the whole
 * string unsplit.
 */
fun string.split(self, sep: string) -> string[] {
    let result = []
    // An empty separator has a match at every position, so `_string_find` always
    // returns 0 and `start` never advances -- an infinite loop. Treat it as no
    // split (the whole string), mirroring `replace`'s empty-`old` guard.
    if len(sep) == 0 {
        result.push(self)
        return result
    }
    // One field per separator boundary: the piece before each match, then the
    // tail after the last one -- so "a,,b" keeps its interior empty field AND a
    // trailing separator yields a trailing empty field ("a," is [a, ""],
    // consistent with the interior behavior). Reaching exactly len(self) means
    // the previous field ended with a separator (or the subject is empty), so
    // the empty tail is still a field; a no-match tail jumps past it.
    let start: int64 = 0
    while start <= len(self) {
        if start == len(self) {
            result.push("")
            start = start + 1
        } else {
            let rest = _string_slice(self, start, len(self))
            let pos = _string_find(rest, sep)
            if pos != null {
                result.push(_string_slice(self, start, start + pos))
                start = start + pos + len(sep)
            } else {
                result.push(_string_slice(self, start, len(self)))
                start = len(self) + 1
            }
        }
    }
    return result
}

/** A copy of `self` with leading and trailing ASCII whitespace removed. */
// Multibyte-safe: whitespace is always a single byte, so the probes
// advance/retreat one byte at a time, and a probe that lands mid-character
// (`_string_char_at` returns null there) means a multibyte character -- never
// whitespace -- so the scan stops. The null probe is handled with `if let`,
// never compared as a string.
fun string.trim(self) -> string {
    let one: int64 = 1
    let start: int64 = 0
    let end = len(self)
    while start < end {
        if let c = _string_char_at(self, start) {
            if c == " " || c == "\t" || c == "\n" || c == "\r" {
                start += one
            } else {
                break
            }
        } else {
            break
        }
    }
    while end > start {
        if let c = _string_char_at(self, end - one) {
            if c == " " || c == "\t" || c == "\n" || c == "\r" {
                end -= one
            } else {
                break
            }
        } else {
            break
        }
    }
    return _string_slice(self, start, end)
}

/** Whether `self` begins with `prefix`. */
fun string.starts_with(self, prefix: string) -> bool {
    if len(prefix) > len(self) {
        return false
    }
    return _string_slice(self, 0, len(prefix)) == prefix
}

/** Whether `self` ends with `suffix`. */
fun string.ends_with(self, suffix: string) -> bool {
    if len(suffix) > len(self) {
        return false
    }
    return _string_slice(self, len(self) - len(suffix), len(self)) == suffix
}

/**
 * The byte offset of the first occurrence of substring `sub`, or null if
 * absent. Use `s.find(sub) != null` for a substring test; the array method
 * `contains` compares whole elements, not substrings.
 */
fun string.find(self, sub: string) -> int64? {
    return _string_find(self, sub)
}

/** A copy of `self` with every occurrence of `old` replaced by `new`. */
fun string.replace(self, old: string, new: string) -> string {
    if len(old) == 0 {
        return self
    }
    let result = ""
    let start: int64 = 0
    while start < len(self) {
        let rest = _string_slice(self, start, len(self))
        let pos = _string_find(rest, old)
        if pos != null {
            result = result + _string_slice(self, start, start + pos) + new
            start = start + pos + len(old)
        } else {
            result = result + _string_slice(self, start, len(self))
            start = len(self)
        }
    }
    return result
}

/**
 * The characters of `self` as a one-string-per-character array. Multibyte
 * UTF-8 characters are kept whole.
 */
fun string.chars(self) -> string[] {
    let result = []
    let i: int64 = 0
    while i < len(self) {
        if let c = _string_char_at(self, i) {
            result.push(c)
            i += len(c)
        } else {
            break
        }
    }
    return result
}

/** Join the string elements of `self` with `sep` between each. */
fun string[].join(self, sep: string) -> string {
    let result = ""
    let first = true
    for p in self {
        if first {
            result = result + p
            first = false
        } else {
            result = result + sep + p
        }
    }
    return result
}

/** A copy of `self` with ASCII letters upper-cased; other characters are unchanged. */
// Implemented over the UTF-8 byte view. An ASCII case change preserves UTF-8
// validity, so the byte->string conversion cannot fail; matching (rather than
// `!`) keeps `to_upper` non-fallible, returning `string` not `string!`.
fun string.to_upper(self) -> string {
    let bytes = _string_bytes(self)
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
        Err { error } => self,
    }
}

/** A copy of `self` with ASCII letters lower-cased; other characters are unchanged. */
fun string.to_lower(self) -> string {
    let bytes = _string_bytes(self)
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
        Err { error } => self,
    }
}
