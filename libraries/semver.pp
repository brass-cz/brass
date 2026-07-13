// Semantic Versioning 2.0.0 (https://semver.org): parse a version string into a
// `Version`, render it back, and order two of them by the spec's precedence
// rules.
//
//     import semver.{ Version }
//
//     const v = Version.parse("1.4.2-rc.1+build.5")!
//     println("{v.major}.{v.minor}.{v.patch}")     // 1.4.2
//     println(v.compare(Version.parse("1.4.2")!))  // -1: a pre-release is LOWER
//
// Pure prepoly on top of the `regex` library -- no native half of its own, so it
// needs no plugin beyond the regex one. Parsing uses the OFFICIAL pattern from
// semver.org verbatim (see `_PATTERN`), which is what makes acceptance exactly
// the spec's: no leading zeros in the numeric fields, a pre-release of
// dot-separated identifiers, and optional build metadata.
//
//     PREPOLY_INCLUDE=/path/to/libraries
//     import semver.{ Version }
//
// The regex plugin must be built once (`libraries/build.sh`).

import regex.{ Regex, Match }

// The official regular expression from semver.org, transcribed for a prepoly
// string literal: every backslash is doubled (a prepoly string is not raw).
// The pattern has no `{n}` repetition, so no brace needs escaping here -- but
// see `libraries/regex.pp` on that hazard before editing this.
//
// It is anchored (`^`/`$`), so `find` accepts only a string that is a version
// in its entirety, and it names every field, so the parse below reads the
// components by name rather than by counting parentheses.
const _PATTERN = "^(?P<major>0|[1-9]\\d*)\\.(?P<minor>0|[1-9]\\d*)\\.(?P<patch>0|[1-9]\\d*)(?:-(?P<prerelease>(?:0|[1-9]\\d*|\\d*[a-zA-Z-][0-9a-zA-Z-]*)(?:\\.(?:0|[1-9]\\d*|\\d*[a-zA-Z-][0-9a-zA-Z-]*))*))?(?:\\+(?P<buildmetadata>[0-9a-zA-Z-]+(?:\\.[0-9a-zA-Z-]+)*))?$"

// Compiled once, at module load: a `Regex` is expensive to build and cheap to
// keep, and the regex library never releases one. A pattern written here cannot
// fail to compile, so the `!` at the top level is unreachable in practice.
const _VERSION = Regex.new(_PATTERN)!

/**
 * A parsed semantic version.
 *
 * `prerelease` and `build` are null when the version carries none -- which is
 * not the same as an empty one, a form the grammar does not admit. Both keep
 * their raw text (`"rc.1"`, `"build.5"`); `prerelease_ids` splits the
 * pre-release into the identifiers precedence compares.
 */
type Version = {
    major: int64
    minor: int64
    patch: int64
    prerelease: string?
    build: string?
}

/**
 * The version `text` denotes. Fails when `text` is not a semantic version in
 * its entirety (the official pattern is anchored): a leading `v`, a missing
 * field, a leading zero, or trailing text are all rejected.
 */
fun Version.parse(text: string) -> Version! {
    if let m = _VERSION.find(text) {
        return Self {
            major: _number(m, "major")!,
            minor: _number(m, "minor")!,
            patch: _number(m, "patch")!,
            prerelease: _optional(m, "prerelease"),
            build: _optional(m, "buildmetadata"),
        }
    }
    return error("not a semantic version: `{text}`")
}

/** The version `major.minor.patch`, with no pre-release and no build metadata. */
fun Version.new(major: int64, minor: int64, patch: int64) -> Version {
    return Self {
        major: major,
        minor: minor,
        patch: patch,
        prerelease: null,
        build: null,
    }
}

/**
 * The version as text, in the form the grammar defines -- so parsing the result
 * yields an equal version, and a version that was parsed renders back to what it
 * was parsed from.
 */
fun Version.to_string(self) -> string {
    let out = "{self.major}.{self.minor}.{self.patch}"
    const pre = self.prerelease
    if pre {
        out = "{out}-{pre}"
    }
    const build = self.build
    if build {
        out = "{out}+{build}"
    }
    return out
}

/** Whether this version carries a pre-release, and so precedes its release. */
fun Version.is_prerelease(self) -> bool {
    const pre = self.prerelease
    if pre {
        return true
    }
    return false
}

/**
 * The pre-release identifiers, in order (`"rc.1"` -> `["rc", "1"]`), or an
 * empty array when there is no pre-release. These are what `compare` orders.
 */
fun Version.prerelease_ids(self) -> string[] {
    const pre = self.prerelease
    if pre {
        return pre.split(".")
    }
    let none: string[] = []
    return none
}

/**
 * Order two versions by the spec's precedence rules (§11): -1 when `self`
 * precedes `other`, 0 when neither precedes the other, 1 when `self` follows.
 *
 * Major, minor, and patch compare numerically. A version WITH a pre-release
 * precedes the same version without one (`1.0.0-rc.1` < `1.0.0`). Two
 * pre-releases compare identifier by identifier, left to right: a numeric
 * identifier compares numerically and precedes an alphanumeric one, which
 * compares by ASCII order; if all the identifiers of the shorter one are equal,
 * the shorter one precedes.
 *
 * BUILD METADATA IS IGNORED (§10): `1.0.0+a` and `1.0.0+b` neither precedes the
 * other, so this returns 0 for them -- they are the same version, differently
 * built.
 */
fun Version.compare(self, other: Version) -> int64 {
    const major = _cmp_int(self.major, other.major)
    if major != 0 {
        return major
    }
    const minor = _cmp_int(self.minor, other.minor)
    if minor != 0 {
        return minor
    }
    const patch = _cmp_int(self.patch, other.patch)
    if patch != 0 {
        return patch
    }
    return _cmp_prerelease(self.prerelease_ids(), other.prerelease_ids())
}

/**
 * Whether the two versions have the same precedence. Build metadata is ignored
 * (see `compare`), so `1.0.0+a` equals `1.0.0+b`; compare `to_string()` for
 * textual identity.
 */
fun Version.equals(self, other: Version) -> bool {
    return self.compare(other) == 0
}

/** Whether this version precedes `other` (see `compare`). */
fun Version.less_than(self, other: Version) -> bool {
    return self.compare(other) < 0
}

/** Whether this version follows `other` (see `compare`). */
fun Version.greater_than(self, other: Version) -> bool {
    return self.compare(other) > 0
}

/**
 * A copy of `versions` in ascending precedence order (see `compare`), leaving
 * the argument untouched. Versions of equal precedence keep their relative
 * order.
 */
// Insertion sort, like the prelude's `array.sort` -- which cannot be used here:
// it orders with `<`, which records do not support.
fun sort(versions: Version[]) -> Version[] {
    let out: Version[] = []
    for v in versions {
        out.push(v)
    }
    let i: int64 = 1
    while i < len(out) {
        const key = out[i]
        let j = i - 1
        while j >= 0 && out[j].compare(key) > 0 {
            out[j + 1] = out[j]
            j -= 1
        }
        out[j + 1] = key
        i += 1
    }
    return out
}

// A group the pattern requires: absent means the pattern was edited into
// something that no longer names it, not that the input was odd.
fun _number(m: Match, name: string) -> int64! {
    if let g = m.named(name) {
        match int64.parse(g.text) {
            Ok { value } => {
                return value
            }
            Err { error: e } => {
                return error("`{name}` does not fit in an int64: {g.text}")
            }
        }
    }
    return error("the semver pattern names no group `{name}`")
}

// An optional group: absent -> null (the grammar admits no empty one, so null
// and "" never both mean the same thing).
fun _optional(m: Match, name: string) -> string? {
    if let g = m.named(name) {
        return g.text
    }
    return null
}

fun _cmp_int(a: int64, b: int64) -> int64 {
    if a < b {
        return -1
    }
    if a > b {
        return 1
    }
    return 0
}

// The pre-release rule (§11.3-11.4). An EMPTY identifier list means "no
// pre-release", which has the HIGHER precedence -- the one place where having
// less means being more.
fun _cmp_prerelease(a: string[], b: string[]) -> int64 {
    if len(a) == 0 && len(b) == 0 {
        return 0
    }
    if len(a) == 0 {
        return 1
    }
    if len(b) == 0 {
        return -1
    }
    let i: int64 = 0
    while i < len(a) && i < len(b) {
        const ord = _cmp_identifier(a[i], b[i])
        if ord != 0 {
            return ord
        }
        i += 1
    }
    // Every identifier they share is equal: the shorter list precedes.
    return _cmp_int(len(a), len(b))
}

// One pre-release identifier. Numeric identifiers compare numerically and
// always precede alphanumeric ones; alphanumeric identifiers compare in ASCII
// order.
fun _cmp_identifier(a: string, b: string) -> int64 {
    const a_num = _is_numeric(a)
    const b_num = _is_numeric(b)
    if a_num && !b_num {
        return -1
    }
    if !a_num && b_num {
        return 1
    }
    if a_num && b_num {
        // The grammar forbids a leading zero, so a longer numeric identifier is
        // the larger number and equal lengths compare digit by digit. Comparing
        // this way rather than parsing keeps the ordering total for identifiers
        // too large for an int64.
        const by_width = _cmp_int(len(a), len(b))
        if by_width != 0 {
            return by_width
        }
    }
    return _string_cmp(a, b)
}

// Whether every character is a digit. The identifier grammar is ASCII, so
// examining bytes is examining characters.
fun _is_numeric(id: string) -> bool {
    if len(id) == 0 {
        return false
    }
    for b in to_bytes(id) {
        if b < 48 || b > 57 {
            return false
        }
    }
    return true
}
