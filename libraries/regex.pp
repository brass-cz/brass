// Regular expressions: compile a pattern once into a `Regex`, then test, find,
// replace, or split with it.
//
//     import regex.{ Regex }
//
//     const date = Regex.new("(?<year>\\d\{4})-(\\d\{2})-(\\d\{2})")!
//     if let m = date.find("due 2026-07-13, ok") {
//         println(m.text)                       // 2026-07-13
//         if let y = m.named("year") { println(y.text) }   // 2026
//     }
//
// WRITING A PATTERN. A prepoly string literal is not raw: it interprets `\` and
// it INTERPOLATES `{expr}`. So a pattern needs two things escaped, and the
// second one bites silently:
//
//   - a backslash doubles: `\\d`, `\\w`, `\\b`, `\\.`;
//   - an opening brace is escaped `\{` -- `"\\d{4}"` does NOT mean "four
//     digits", it interpolates the expression `4` and compiles as `\d4` (a
//     digit followed by the character `4`). Write `"\\d\{4}"`. A closing brace
//     needs nothing. Quantifiers with a comma (`{2,3}`) are a syntax error
//     rather than a silent change, but escape them the same way: `\{2,3}`.
//
// The same applies to a replacement string: prefer `$name` and `$1` over the
// braced `${name}` form, which would have to be written `$\{name}`.
//
// The engine is Rust's `regex`: a finite automaton, so matching is LINEAR in
// the length of the subject however the pattern is written -- a regex over
// untrusted input cannot blow up the way a backtracking engine does. The price
// is that backreferences (`\1`) and lookaround (`(?=..)`, `(?<=..)`) do not
// exist here: neither is expressible in an automaton, and a pattern using one
// fails to compile rather than silently meaning something else.
//
// Supported syntax is the usual set: character classes and Unicode classes
// (`\d`, `\w`, `[[:alpha:]]`, `\p{Greek}`), repetition (`*`, `+`, `?`, `{m,n}`,
// each with a lazy `?` form), alternation, anchors (`^`, `$`, `\b`), groups
// (`(..)`), non-capturing groups (`(?:..)`), named groups (`(?<name>..)`), and
// inline flags (`(?i)` case-insensitive, `(?m)` multi-line, `(?s)` dot matches
// newline, `(?x)` ignore whitespace).
//
// Offsets are UTF-8 BYTE offsets, as everywhere else in prepoly, so `Match.start`
// agrees with `len` and `string.find`.
//
// This is a library rather than part of `std`: the engine is native code behind
// a plugin. Point `PREPOLY_INCLUDE` at this directory and import it:
//
//     PREPOLY_INCLUDE=/path/to/libraries
//     import regex.{ Regex }
//
// Build the plugin once with `libraries/build.sh`.
//
// A compiled `Regex` is never released (the language has no destructors), so
// compile a pattern ONCE and keep it -- compiling inside a loop grows the
// process. That is the right way to use any regex engine anyway: compilation is
// far more expensive than matching.

import libregex.{
    regex_compile,
    regex_group_names,
    regex_is_match,
    regex_find,
    regex_find_all,
    regex_replace,
    regex_split,
    regex_escape,
}

/**
 * One capture group of a match: the text it matched and the byte span it
 * occupies in the subject string, so `subject`'s `[start, end)` bytes are
 * exactly `text`.
 */
type Group = {
    text: string
    start: int64
    end: int64
}

/**
 * One match of a regex against a subject string: the matched text and its byte
 * span, plus the capture groups.
 *
 * `groups[0]` is the whole match (the same text/span as the fields), and
 * `groups[i]` is the i-th `(..)` group in the pattern, left to right by opening
 * parenthesis. A group that did not participate -- the `(a)` of `(a)|(b)`
 * against `"b"` -- is `null`, which is not the same as a group that matched
 * empty. Reach a group by number with `group`, by name with `named`.
 */
type Match = {
    text: string
    start: int64
    end: int64
    groups: Group?[]
    // The group names, positional with `groups` (empty for an unnamed group);
    // `named` searches them. Private: `named` is the surface.
    _names: string[]
}

/**
 * The `index`-th capture group, or null when the group did not participate in
 * this match or the pattern has no such group. `group(0)` is the whole match.
 */
fun Match.group(self, index: int64) -> Group? {
    if index < 0 || index >= len(self.groups) {
        return null
    }
    return self.groups[index]
}

/**
 * The capture group named `name` (from a `(?<name>..)` group), or null when it
 * did not participate or the pattern has no such group.
 */
fun Match.named(self, name: string) -> Group? {
    let i: int64 = 0
    while i < len(self._names) {
        if self._names[i] == name {
            return self.groups[i]
        }
        i += 1
    }
    return null
}

/**
 * A compiled regular expression. Build one with `Regex.new`, which is where a
 * bad pattern is reported; every method below is infallible.
 */
type Regex = {
    // The pattern as it was compiled, so a `Regex` prints as something a reader
    // can recognize.
    pattern: string
    _handle: int64
    _names: string[]
}

/**
 * Compile `pattern`. Fails on a pattern the engine rejects: bad syntax, a
 * backreference or lookaround (this engine has neither -- see the module
 * comment), or a repetition whose compiled form is too large.
 */
fun Regex.new(pattern: string) -> Regex! {
    const handle = regex_compile(pattern)!
    return Self {
        pattern: pattern,
        _handle: handle,
        _names: regex_group_names(handle),
    }
}

/**
 * The number of capture groups, COUNTING group 0 (the whole match): a pattern
 * with no `(..)` groups answers 1.
 */
fun Regex.group_count(self) -> int64 {
    return len(self._names)
}

/**
 * Whether the regex matches anywhere in `text`. Cheaper than `find` -- the
 * engine stops at the first match and records no groups -- so prefer it when
 * the match itself is not wanted.
 */
fun Regex.is_match(self, text: string) -> bool {
    return regex_is_match(self._handle, text)
}

/** The leftmost match in `text`, or null when there is none. */
fun Regex.find(self, text: string) -> Match? {
    return self.find_from(text, 0)
}

/**
 * The leftmost match starting at or after byte offset `from`, or null when
 * there is none.
 *
 * `from` moves where the SEARCH starts, not where the string starts: `^` still
 * anchors to the real beginning of `text`, and `\b` still sees the character
 * before `from`. Resuming from a previous match's `end` therefore walks the
 * same matches `find_all` returns.
 */
fun Regex.find_from(self, text: string, from: int64) -> Match? {
    const spans = regex_find(self._handle, text, from)
    if len(spans) == 0 {
        return null
    }
    return _match_at(text, spans, 0, self._names)
}

/**
 * Every non-overlapping match in `text`, leftmost-first. Each match's search
 * resumes where the previous one ended, so overlapping candidates are not
 * reported (`"aa"` matched by `"aa"` against `"aaa"` yields one match, not two).
 */
fun Regex.find_all(self, text: string) -> Match[] {
    const spans = regex_find_all(self._handle, text)
    const stride = len(self._names) * 2
    let out: Match[] = []
    let base: int64 = 0
    while base < len(spans) {
        out.push(_match_at(text, spans, base, self._names))
        base += stride
    }
    return out
}

/**
 * `text` with the FIRST match replaced by `replacement` (the text unchanged
 * when nothing matches). See `replace_all` for what `replacement` may contain.
 */
fun Regex.replace(self, text: string, replacement: string) -> string {
    return regex_replace(self._handle, text, replacement, 1)
}

/**
 * `text` with every match replaced by `replacement`.
 *
 * `replacement` is not a plain string: `$1` (or `${1}`) expands to that group's
 * text, `$name` (or `${name}`) to that named group's, and `$$` to a literal
 * `$`. A group that did not participate expands to nothing. Braces disambiguate
 * where a name would otherwise run on -- `${1}0` is group 1 followed by a zero,
 * while `$10` is group 10.
 */
fun Regex.replace_all(self, text: string, replacement: string) -> string {
    return regex_replace(self._handle, text, replacement, 0)
}

/**
 * `text` split around every match, in order. A match at either end, or two
 * adjacent matches, yield empty fields -- as `string.split` does -- so the
 * result always holds one more field than there were matches.
 */
fun Regex.split(self, text: string) -> string[] {
    return regex_split(self._handle, text)
}

/**
 * `text` with every regex metacharacter escaped, so the result is a pattern
 * matching `text` literally. Use it to build a pattern around text the program
 * did not write (a user's search term), where a stray `(` would otherwise be a
 * compile error and a `.` would match too much.
 */
fun escape(text: string) -> string {
    return regex_escape(text)
}

// One match from the flat span run the plugin returns: the group spans occupy
// `spans[base .. base + 2 * len(names)]`, a `(start, end)` pair per group, with
// `(-1, -1)` for a group that did not participate. The text is sliced HERE
// rather than in the plugin so a match crossing the boundary is a pair of
// offsets, not a copy of every group's bytes -- and the offsets stay available
// to a caller that wants them.
fun _match_at(text: string, spans: int64[], base: int64, names: string[]) -> Match {
    let groups: Group?[] = []
    let i: int64 = 0
    while i < len(names) {
        const start = spans[base + i * 2]
        const end = spans[base + i * 2 + 1]
        if start < 0 {
            groups.push(null)
        } else {
            // The engine's offsets always fall on character boundaries.
            groups.push(Group { text: _string_slice(text, start, end), start: start, end: end })
        }
        i += 1
    }
    // Group 0 always participates, so its span is the match's own.
    const start = spans[base]
    const end = spans[base + 1]
    return Match {
        text: _string_slice(text, start, end),
        start: start,
        end: end,
        groups: groups,
        _names: names,
    }
}
