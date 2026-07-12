// TOML: a value tree, a recursive-descent parser, accessors, a serializer, and a
// reflective decoder into typed structures. A library (pure prepoly, no plugin) --
// import it explicitly:
//
//     import data.toml.{ TomlValue, parse }
//
// The value tree mirrors TOML's scalar and container kinds. A Table keeps its
// entries in a string -> TomlValue `HashMap` (the `_TomlTable` refinement below
// pins the slots), so lookups are hash lookups and nested tables are built by
// navigating those maps in place. Two consequences of the map storage: `stringify`
// renders a table's entries in the map's slot order, not the source document's
// order; and dates/times are kept verbatim as text in a `Datetime`, since the
// tree carries no calendar type.
//
// The parser accepts the common TOML surface: comments, bare/quoted/dotted keys,
// basic and literal strings (single- and multi-line), integers (decimal with
// separators and sign, plus `0x`/`0o`/`0b`), floats (fractional, exponent,
// `inf`/`nan`), booleans, arrays, inline tables, `[table]` headers and `[[array
// of tables]]` headers. Offset/local date-times, dates and times are recognized
// structurally and stored as `Datetime` strings without calendar validation.
//
// Table navigation deliberately uses FREE functions over the `_TomlTable` map
// (`_child`, `_append_array_table`) rather than methods that return the map: a
// method returning the map-refinement type does not resolve at its call site under
// the current checker, so the map type is only ever produced by free functions and
// the parser's cursor methods return only scalars, strings, and `TomlValue`s.

import std.collections.HashMap

type _TomlTable = HashMap {
    key: string
    value: TomlValue
}

/**
 * A parsed TOML value, one variant per TOML kind. Obtain the document root (a
 * `Table`) with `parse`, inspect it with the accessors (`get`, `at`, `as_*`),
 * decode it into a typed structure with `into`, and render it back to text with
 * `stringify`. A `Datetime` holds the source date/time text verbatim.
 */
type TomlValue =
    | String { value: string }
    | Integer { value: int64 }
    | Float { value: float64 }
    | Bool { value: bool }
    | Datetime { value: string }
    | Array { value: TomlValue[] }
    | Table { values: _TomlTable }

// ----- accessors -----

/** The string inside a `String`, or an error for any other kind. */
fun TomlValue.as_string(self) -> string! {
    match self {
        TomlValue.String { value } => { return value }
        _ => {}
    }
    return error("expected a TOML string")
}

/** The integer inside an `Integer`, or an error for any other kind. */
fun TomlValue.as_integer(self) -> int64! {
    match self {
        TomlValue.Integer { value } => { return value }
        _ => {}
    }
    return error("expected a TOML integer")
}

/** The number inside a `Float`, or an error for any other kind. */
fun TomlValue.as_float(self) -> float64! {
    match self {
        TomlValue.Float { value } => { return value }
        _ => {}
    }
    return error("expected a TOML float")
}

/** The boolean inside a `Bool`, or an error for any other kind. */
fun TomlValue.as_bool(self) -> bool! {
    match self {
        TomlValue.Bool { value } => { return value }
        _ => {}
    }
    return error("expected a TOML boolean")
}

/** The verbatim date/time text inside a `Datetime`, or an error otherwise. */
fun TomlValue.as_datetime(self) -> string! {
    match self {
        TomlValue.Datetime { value } => { return value }
        _ => {}
    }
    return error("expected a TOML date-time")
}

/** Whether this value is a `Table`. */
fun TomlValue.is_table(self) -> bool {
    match self {
        TomlValue.Table { values } => { return true }
        _ => {}
    }
    return false
}

/** The value of table entry `key`, or an error naming the missing key. */
fun TomlValue.get(self, key: string) -> TomlValue! {
    match self {
        TomlValue.Table { values } => {
            if let v = values.get(key) {
                return v
            }
            return error("missing key '{key}'")
        }
        _ => {}
    }
    return error("expected a TOML table")
}

/** The element at `index` of an array, or an error when out of range. */
fun TomlValue.at(self, index: int64) -> TomlValue! {
    match self {
        TomlValue.Array { value } => {
            if index >= 0 && index < len(value) {
                return value[index]
            }
            return error("array index {index} out of range")
        }
        _ => {}
    }
    return error("expected a TOML array")
}

// `as_array` and `keys` are free functions, not methods: a method returning an
// array type does not resolve at its call site under the current checker (the
// result reads back as `never`), whereas a free function does.

/** The elements of an `Array` value, or an error for any other kind. */
fun as_array(value: TomlValue) -> TomlValue[]! {
    match value {
        TomlValue.Array { value } => { return value }
        _ => {}
    }
    return error("expected a TOML array")
}

/** The keys of a `Table` value, in the map's (unspecified) slot order. */
fun keys(value: TomlValue) -> string[]! {
    match value {
        TomlValue.Table { values } => { return values.keys() }
        _ => {}
    }
    return error("expected a TOML table")
}

// ----- reflective decoding -----

/**
 * Decode `self` into the type the call site expects, driven entirely by that
 * target type: `const c: Config = t.into()!`. A scalar target reads the matching
 * TOML scalar; a record target walks its own fields (each decoded recursively). A
 * TOML value of the wrong kind for the target is a runtime decode error. Arrays
 * cannot be decoded into a scalar or record target (there is no typed-array
 * target support), so use `as_array` and decode elements yourself.
 */
fun TomlValue.into(self) -> infer! {
    match self {
        TomlValue.Integer { value } => { return infer.from(value) }
        TomlValue.Float { value } => { return infer.from(value) }
        TomlValue.String { value } => { return infer.from(value) }
        TomlValue.Datetime { value } => { return infer.from(value) }
        TomlValue.Bool { value } => { return infer.from(value) }
        TomlValue.Table { values } => {
            let ret: infer
            for field in fields(ret) {
                ret[field] = self.get(field)!.into()!
            }
            return ret
        }
        TomlValue.Array { value } => {
            return error("cannot decode a TOML array into a scalar or record")
        }
    }
}


// ----- serialization -----
//
// `stringify` renders the top-level table as `key = value` lines; nested tables
// and arrays render in inline form (`{ .. }` / `[ .. ]`), so the whole document
// is valid TOML on a bounded number of lines. `_inline` is the recursive renderer
// and, like json's `stringify`, is a FREE function rather than a method: the
// checker's per-call re-elaboration does not converge for a self-recursive method
// over a sum this wide, but a free function recursing by name does.

/** Render a `TomlValue` back to TOML text. A `Table` becomes `key = value` lines;
 * every other kind (and every nested value) renders in inline form. */
fun stringify(value: TomlValue) -> string {
    match value {
        TomlValue.Table { values } => {
            let out = ""
            for k in values.keys() {
                if let v = values.get(k) {
                    out = out + _key_str(k) + " = " + _inline(v) + "\n"
                }
            }
            return out
        }
        _ => {}
    }
    return _inline(value)
}

// Render any value in single-expression (inline) form: scalars as literals, an
// array as `[a, b]`, a table as `{ k = v }`. Recurses by name (see the note on
// `stringify`).
fun _inline(value: TomlValue) -> string {
    match value {
        TomlValue.String { value } => { return _quote(value) }
        TomlValue.Integer { value } => { return "{value}" }
        TomlValue.Float { value } => { return "{value}" }
        TomlValue.Bool { value } => {
            if value { return "true" }
            return "false"
        }
        TomlValue.Datetime { value } => { return value }
        TomlValue.Array { value } => {
            let out = "["
            let first = true
            for elem in value {
                if !first { out = out + ", " }
                out = out + _inline(elem)
                first = false
            }
            return out + "]"
        }
        TomlValue.Table { values } => {
            let out = "\{ "
            let first = true
            for k in values.keys() {
                if !first { out = out + ", " }
                if let v = values.get(k) {
                    out = out + _key_str(k) + " = " + _inline(v)
                }
                first = false
            }
            return out + " \}"
        }
    }
}

// A key rendered for output: bare if it is a valid bare key, else quoted.
fun _key_str(k: string) -> string {
    if _is_bare_key(k) {
        return k
    }
    return _quote(k)
}

// Wrap a string in double quotes with the TOML basic-string escapes the parser
// accepts. Iterated by byte index rather than `s.chars()` on purpose: the
// checker's per-call re-elaboration does not converge when a recursive renderer
// calls a helper that in turn builds an inferred `[]` array (as `chars` does), so
// this stays index-based.
fun _quote(s: string) -> string {
    let out = "\""
    let i: int64 = 0
    while i < len(s) {
        if let ch = _string_char_at(s, i) {
            if ch == "\"" {
                out = out + "\\\""
            } else if ch == "\\" {
                out = out + "\\\\"
            } else if ch == "\n" {
                out = out + "\\n"
            } else if ch == "\t" {
                out = out + "\\t"
            } else if ch == "\r" {
                out = out + "\\r"
            } else {
                out = out + ch
            }
            i = i + len(ch)
        } else {
            i = i + 1
        }
    }
    return out + "\""
}

// ----- parsing -----
//
// A single-pass recursive-descent parser. `_Cursor` carries the text and the
// current byte offset; its methods advance it and return scalars/strings/values.
// `parse` walks statements (key/value pairs, `[table]` headers, `[[array of
// tables]]` headers), building the tree into a root `_TomlTable` and tracking a
// `current` table that bare key/value pairs are stored into. Dotted keys are read
// one part at a time and navigated with the free `_child`.

type _Cursor = {
    text: string
    pos: int64
}

/**
 * Parse `text` as a TOML document, returning its root as a `Table`. Errors on the
 * first malformed statement, naming the byte offset.
 */
fun parse(text: string) -> TomlValue! {
    let cur = _Cursor { text: text, pos: 0 }
    let root: _TomlTable = HashMap.new()
    let current = root
    while cur.pos < len(cur.text) {
        cur._skip_blank()
        if cur.pos >= len(cur.text) {
            break
        }
        const c = cur._peek()
        if c == "[" {
            if cur._peek_at(cur.pos + 1) == "[" {
                // `[[a.b]]`: navigate/create the parent of the last segment,
                // append a fresh table to the array there, make it current.
                cur.pos += 2
                let parent = root
                cur._skip_inline_ws()
                let part = cur._key_part()!
                cur._skip_inline_ws()
                while cur._peek() == "." {
                    cur.pos += 1
                    cur._skip_inline_ws()
                    parent = _child(parent, part)!
                    part = cur._key_part()!
                    cur._skip_inline_ws()
                }
                if !cur._starts_with_here("]]") {
                    return error("expected ']]' to close an array-of-tables header at offset {cur.pos}")
                }
                cur.pos += 2
                current = _append_array_table(parent, part)!
            } else {
                // `[a.b.c]`: navigate/create the table at the dotted path from
                // root and make it current.
                cur.pos += 1
                current = root
                cur._skip_inline_ws()
                let part = cur._key_part()!
                current = _child(current, part)!
                cur._skip_inline_ws()
                while cur._peek() == "." {
                    cur.pos += 1
                    cur._skip_inline_ws()
                    part = cur._key_part()!
                    current = _child(current, part)!
                    cur._skip_inline_ws()
                }
                if cur._peek() != "]" {
                    return error("expected ']' to close a table header at offset {cur.pos}")
                }
                cur.pos += 1
            }
        } else {
            // `key = value` (dotted key): navigate `current` to the table holding
            // the final key part, then store the value.
            let tbl = current
            let key = cur._key_part()!
            cur._skip_inline_ws()
            while cur._peek() == "." {
                cur.pos += 1
                cur._skip_inline_ws()
                tbl = _child(tbl, key)!
                key = cur._key_part()!
                cur._skip_inline_ws()
            }
            if cur._peek() != "=" {
                return error("expected '=' after key at offset {cur.pos}")
            }
            cur.pos += 1
            cur._skip_inline_ws()
            const value = cur._value()!
            tbl.set(key, value)
        }
        // A statement must end at a line boundary: only whitespace and a comment
        // may follow it on the line.
        cur._skip_inline_ws()
        cur._skip_comment()
        if cur.pos < len(cur.text) {
            const nl = cur._expect_newline()!
        }
    }
    return TomlValue.Table { values: root }
}

// The child table at `key` of `parent`, creating an empty one when absent. When
// `key` already holds an array of tables, the LAST element is returned -- this is
// how `[a.b]` after `[[a]]` addresses the most recent `a`. A non-table value at
// `key` is an error. A free function on purpose: see the module comment.
fun _child(parent: _TomlTable, key: string) -> _TomlTable! {
    if let existing = parent.get(key) {
        match existing {
            TomlValue.Table { values } => { return values }
            TomlValue.Array { value } => {
                if len(value) > 0 {
                    const last = value[len(value) - 1]
                    match last {
                        TomlValue.Table { values } => { return values }
                        _ => {}
                    }
                }
                return error("key '{key}' is an array, not a table")
            }
            _ => { return error("key '{key}' already holds a non-table value") }
        }
    }
    let t: _TomlTable = HashMap.new()
    parent.set(key, TomlValue.Table { values: t })
    return t
}

// Append a fresh table to the array of tables at `key` of `parent` (creating the
// array if absent) and return the new table. A non-array value at `key` is an
// error.
fun _append_array_table(parent: _TomlTable, key: string) -> _TomlTable! {
    let arr: TomlValue[] = []
    if let existing = parent.get(key) {
        match existing {
            TomlValue.Array { value } => { arr = value }
            _ => { return error("key '{key}' is not an array of tables") }
        }
    }
    let t: _TomlTable = HashMap.new()
    arr.push(TomlValue.Table { values: t })
    parent.set(key, TomlValue.Array { value: arr })
    return t
}

// One key part: a bare key, or a basic/literal quoted key.
fun _Cursor._key_part(self) -> string! {
    const c = self._peek()
    if c == "\"" {
        return self._basic_string()!
    }
    if c == "'" {
        return self._literal_string()!
    }
    const start = self.pos
    while self.pos < len(self.text) && _is_bare_key_char(self._peek()) {
        self.pos += 1
    }
    if self.pos == start {
        return error("expected a key at offset {self.pos}")
    }
    return _string_slice(self.text, start, self.pos)
}

fun _Cursor._value(self) -> TomlValue! {
    const c = self._peek()
    if c == "\"" {
        if self._starts_with_here("\"\"\"") {
            return TomlValue.String { value: self._ml_basic_string()! }
        }
        return TomlValue.String { value: self._basic_string()! }
    }
    if c == "'" {
        if self._starts_with_here("'''") {
            return TomlValue.String { value: self._ml_literal_string()! }
        }
        return TomlValue.String { value: self._literal_string()! }
    }
    if c == "[" {
        return self._array()!
    }
    if c == "\{" {
        return self._inline_table()!
    }
    if c == "t" || c == "f" {
        return self._bool()!
    }
    return self._number_or_datetime()!
}

fun _Cursor._bool(self) -> TomlValue! {
    if self._starts_with_here("true") {
        self.pos += 4
        return TomlValue.Bool { value: true }
    }
    if self._starts_with_here("false") {
        self.pos += 5
        return TomlValue.Bool { value: false }
    }
    return error("invalid literal at offset {self.pos}")
}

fun _Cursor._array(self) -> TomlValue! {
    self.pos += 1
    let items: TomlValue[] = []
    while true {
        self._skip_blank()
        const c = self._peek()
        if c == "]" {
            self.pos += 1
            return TomlValue.Array { value: items }
        }
        if c == "" {
            return error("unterminated array")
        }
        const v = self._value()!
        items.push(v)
        self._skip_blank()
        const sep = self._peek()
        if sep == "," {
            self.pos += 1
        } else if sep == "]" {
            self.pos += 1
            return TomlValue.Array { value: items }
        } else {
            return error("expected ',' or ']' in array at offset {self.pos}")
        }
    }
    return error("unterminated array")
}

fun _Cursor._inline_table(self) -> TomlValue! {
    self.pos += 1
    let t: _TomlTable = HashMap.new()
    self._skip_inline_ws()
    if self._peek() == "\}" {
        self.pos += 1
        return TomlValue.Table { values: t }
    }
    while true {
        self._skip_inline_ws()
        let tbl = t
        let key = self._key_part()!
        self._skip_inline_ws()
        while self._peek() == "." {
            self.pos += 1
            self._skip_inline_ws()
            tbl = _child(tbl, key)!
            key = self._key_part()!
            self._skip_inline_ws()
        }
        if self._peek() != "=" {
            return error("expected '=' in inline table at offset {self.pos}")
        }
        self.pos += 1
        self._skip_inline_ws()
        const v = self._value()!
        tbl.set(key, v)
        self._skip_inline_ws()
        const sep = self._peek()
        self.pos += 1
        if sep == "\}" {
            return TomlValue.Table { values: t }
        }
        if sep != "," {
            return error("expected ',' or '\}' in inline table at offset {self.pos}")
        }
    }
    return error("unterminated inline table")
}

// ----- strings -----

fun _Cursor._basic_string(self) -> string! {
    self.pos += 1
    let out = ""
    while self.pos < len(self.text) {
        const c = self._peek()
        self.pos += 1
        if c == "\"" {
            return out
        }
        if c == "\n" {
            return error("newline in a single-line string at offset {self.pos}")
        }
        if c == "\\" {
            out = out + self._escape()!
        } else {
            out = out + c
        }
    }
    return error("unterminated string")
}

fun _Cursor._literal_string(self) -> string! {
    self.pos += 1
    const start = self.pos
    while self.pos < len(self.text) {
        const c = self._peek()
        if c == "'" {
            const out = _string_slice(self.text, start, self.pos)
            self.pos += 1
            return out
        }
        if c == "\n" {
            return error("newline in a single-line literal string at offset {self.pos}")
        }
        self.pos += 1
    }
    return error("unterminated literal string")
}

fun _Cursor._ml_basic_string(self) -> string! {
    self.pos += 3
    self._skip_leading_newline()
    let out = ""
    while self.pos < len(self.text) {
        if self._starts_with_here("\"\"\"") {
            self.pos += 3
            return out
        }
        const c = self._peek()
        if c == "\\" {
            self.pos += 1
            const e = self._peek()
            // A backslash at end of line trims the newline and the leading
            // whitespace of the following lines.
            if e == "\n" || e == "\r" || e == " " || e == "\t" {
                self._skip_ws_and_newlines()
            } else {
                out = out + self._escape()!
            }
        } else {
            self.pos += 1
            out = out + c
        }
    }
    return error("unterminated multi-line string")
}

fun _Cursor._ml_literal_string(self) -> string! {
    self.pos += 3
    self._skip_leading_newline()
    const start = self.pos
    while self.pos < len(self.text) {
        if self._starts_with_here("'''") {
            const out = _string_slice(self.text, start, self.pos)
            self.pos += 3
            return out
        }
        self.pos += 1
    }
    return error("unterminated multi-line literal string")
}

// The character after a `\` in a basic string, resolved to its literal text.
fun _Cursor._escape(self) -> string! {
    const e = self._peek()
    self.pos += 1
    if e == "\"" {
        return "\""
    }
    if e == "\\" {
        return "\\"
    }
    if e == "n" {
        return "\n"
    }
    if e == "t" {
        return "\t"
    }
    if e == "r" {
        return "\r"
    }
    if e == "b" {
        return _byte_char(8)!
    }
    if e == "f" {
        return _byte_char(12)!
    }
    if e == "u" {
        return self._unicode_escape(4)!
    }
    if e == "U" {
        return self._unicode_escape(8)!
    }
    return error("invalid escape '\\{e}' at offset {self.pos}")
}

// Read `n` hex digits and encode the resulting scalar as UTF-8.
fun _Cursor._unicode_escape(self, n: int64) -> string! {
    let cp: int64 = 0
    let i: int64 = 0
    while i < n {
        const c = self._peek()
        self.pos += 1
        const d = _digit_value(c)
        if d < 0 || d >= 16 {
            return error("invalid unicode escape at offset {self.pos}")
        }
        cp = cp * 16 + d
        i += 1
    }
    return _encode_utf8(cp)!
}

// ----- numbers and date-times -----

// A value token beginning with a digit, sign, `inf` or `nan`. TOML lets a single
// space separate the date and time of a date-time, so a bare date directly
// followed by ` <time>` is joined into one `Datetime`.
fun _Cursor._number_or_datetime(self) -> TomlValue! {
    const start = self.pos
    while self.pos < len(self.text) && _is_value_char(self._peek()) {
        self.pos += 1
    }
    const raw = _string_slice(self.text, start, self.pos)
    if _is_date(raw) && self._peek() == " " {
        const after = self._peek_at(self.pos + 1)
        if _is_digit(after) {
            self.pos += 1
            const tstart = self.pos
            while self.pos < len(self.text) && _is_value_char(self._peek()) {
                self.pos += 1
            }
            const tpart = _string_slice(self.text, tstart, self.pos)
            return TomlValue.Datetime { value: raw + " " + tpart }
        }
    }
    if _is_datetime_token(raw) {
        return TomlValue.Datetime { value: raw }
    }
    return _parse_number(raw)!
}

// Classify and parse a non-date-time numeric token into an `Integer` or `Float`.
fun _parse_number(raw: string) -> TomlValue! {
    if raw.starts_with("0x") {
        return TomlValue.Integer { value: _parse_radix(_string_slice(raw, 2, len(raw)), 16)! }
    }
    if raw.starts_with("0o") {
        return TomlValue.Integer { value: _parse_radix(_string_slice(raw, 2, len(raw)), 8)! }
    }
    if raw.starts_with("0b") {
        return TomlValue.Integer { value: _parse_radix(_string_slice(raw, 2, len(raw)), 2)! }
    }
    let cleaned = raw.replace("_", "")
    if _is_float_token(cleaned) {
        // `float64.parse` accepts a leading `+` and `inf`/`nan`; a leading `+` is
        // stripped defensively so `+inf` parses like `inf`.
        if cleaned.starts_with("+") {
            cleaned = _string_slice(cleaned, 1, len(cleaned))
        }
        return TomlValue.Float { value: float64.parse(cleaned)! }
    }
    return TomlValue.Integer { value: int64.parse(cleaned)! }
}

// Parse `digits` (already prefix-stripped) in `base`, ignoring `_` separators.
fun _parse_radix(digits: string, base: int64) -> int64! {
    const clean = digits.replace("_", "")
    if len(clean) == 0 {
        return error("empty integer literal")
    }
    let acc: int64 = 0
    let i: int64 = 0
    while i < len(clean) {
        if let c = _string_char_at(clean, i) {
            const d = _digit_value(c)
            if d < 0 || d >= base {
                return error("invalid digit '{c}' in integer literal")
            }
            acc = acc * base + d
        }
        i += 1
    }
    return acc
}

// ----- cursor primitives -----

fun _Cursor._peek(self) -> string {
    if self.pos >= len(self.text) {
        return ""
    }
    if let c = _string_char_at(self.text, self.pos) {
        return c
    }
    return ""
}

fun _Cursor._peek_at(self, i: int64) -> string {
    if i < 0 || i >= len(self.text) {
        return ""
    }
    if let c = _string_char_at(self.text, i) {
        return c
    }
    return ""
}

fun _Cursor._starts_with_here(self, s: string) -> bool {
    const e = self.pos + len(s)
    if e > len(self.text) {
        return false
    }
    return _string_slice(self.text, self.pos, e) == s
}

// Skip spaces and tabs on the current line only.
fun _Cursor._skip_inline_ws(self) {
    while self.pos < len(self.text) {
        const c = self._peek()
        if c == " " || c == "\t" {
            self.pos += 1
        } else {
            return
        }
    }
}

// Skip a `#` comment to (but not past) the end of its line.
fun _Cursor._skip_comment(self) {
    if self._peek() == "#" {
        while self.pos < len(self.text) && self._peek() != "\n" {
            self.pos += 1
        }
    }
}

// Skip whitespace, newlines, and comments -- used between statements and between
// the elements of a multi-line array.
fun _Cursor._skip_blank(self) {
    while self.pos < len(self.text) {
        const c = self._peek()
        if c == " " || c == "\t" || c == "\n" || c == "\r" {
            self.pos += 1
        } else if c == "#" {
            while self.pos < len(self.text) && self._peek() != "\n" {
                self.pos += 1
            }
        } else {
            return
        }
    }
}

fun _Cursor._skip_ws_and_newlines(self) {
    while self.pos < len(self.text) {
        const c = self._peek()
        if c == " " || c == "\t" || c == "\n" || c == "\r" {
            self.pos += 1
        } else {
            return
        }
    }
}

// Trim the newline that may directly follow a `"""`/`'''` opener.
fun _Cursor._skip_leading_newline(self) {
    if self._peek() == "\r" && self._peek_at(self.pos + 1) == "\n" {
        self.pos += 2
    } else if self._peek() == "\n" {
        self.pos += 1
    }
}

fun _Cursor._expect_newline(self) -> bool! {
    const c = self._peek()
    if c == "\n" {
        self.pos += 1
        return true
    }
    if c == "\r" {
        self.pos += 1
        if self._peek() == "\n" {
            self.pos += 1
        }
        return true
    }
    return error("expected end of line at offset {self.pos}")
}

// ----- character and token classification -----

fun _is_bare_key_char(c: string) -> bool {
    const b = _string_bytes(c)
    if len(b) != 1 {
        return false
    }
    let v: int64 = b[0]
    if v >= 48 && v <= 57 {
        return true
    }
    if v >= 65 && v <= 90 {
        return true
    }
    if v >= 97 && v <= 122 {
        return true
    }
    return v == 45 || v == 95
}

fun _is_bare_key(k: string) -> bool {
    if len(k) == 0 {
        return false
    }
    let i: int64 = 0
    while i < len(k) {
        if let c = _string_char_at(k, i) {
            if !_is_bare_key_char(c) {
                return false
            }
            i += len(c)
        } else {
            return false
        }
    }
    return true
}

// The characters that may appear unquoted in a number or date-time token: bare-key
// characters (digits, letters, `-`, `_`) plus `.`, `:`, and `+`. Space is not
// included; a space inside a date-time is handled specially.
fun _is_value_char(c: string) -> bool {
    if _is_bare_key_char(c) {
        return true
    }
    return c == "." || c == ":" || c == "+"
}

fun _is_digit(c: string) -> bool {
    const b = _string_bytes(c)
    if len(b) != 1 {
        return false
    }
    let v: int64 = b[0]
    return v >= 48 && v <= 57
}

// The numeric value of a single hex-or-decimal digit, or -1 if it is not one.
fun _digit_value(c: string) -> int64 {
    const b = _string_bytes(c)
    if len(b) != 1 {
        return -1
    }
    let v: int64 = b[0]
    if v >= 48 && v <= 57 {
        return v - 48
    }
    if v >= 97 && v <= 102 {
        return v - 87
    }
    if v >= 65 && v <= 70 {
        return v - 55
    }
    return -1
}

// Whether `raw` is a bare TOML date (`YYYY-MM-DD` prefix), used to detect the
// space that may join a date and a time.
fun _is_date(raw: string) -> bool {
    if len(raw) < 10 {
        return false
    }
    if !_is_digit(_string_slice(raw, 0, 1)) {
        return false
    }
    return _string_char_at_eq(raw, 4, "-") && _string_char_at_eq(raw, 7, "-")
}

// Whether `raw` should be read as a date/time: a digit-led token that carries a
// time (`:`) or a full date (`YYYY-MM-DD`).
fun _is_datetime_token(raw: string) -> bool {
    if len(raw) == 0 {
        return false
    }
    if !_is_digit(_string_slice(raw, 0, 1)) {
        return false
    }
    if raw.find(":") != null {
        return true
    }
    return _is_date(raw)
}

// Whether the token is a float rather than an integer: it carries a fractional
// point, an exponent, or is an `inf`/`nan` spelling. (Radix-prefixed integers are
// handled before this is reached, so a hex `e` never lands here.)
fun _is_float_token(s: string) -> bool {
    if s.find(".") != null {
        return true
    }
    if s.find("e") != null || s.find("E") != null {
        return true
    }
    return s.find("inf") != null || s.find("nan") != null
}

fun _string_char_at_eq(s: string, i: int64, expect: string) -> bool {
    if let c = _string_char_at(s, i) {
        return c == expect
    }
    return false
}

// ----- byte / UTF-8 helpers -----

// A byte value as `uint8`, non-fallibly. Every call site passes a value already
// reduced into `0..255`, so the conversion cannot truly fail; folding the fallible
// `uint8.from` in here (rather than propagating it with `!`) keeps `uint8`'s error
// type out of the callers' propagation.
fun _u8(n: int64) -> uint8 {
    match uint8.from(n) {
        Ok { value } => { return value }
        Err { error } => { return 0 }
    }
}

// A byte array decoded as UTF-8 text, or a string error. `_string_from_bytes` is
// consumed with a `match` rather than `!` (as std/string.pp does): propagating its
// error with `!` lets the checker infer this function's error type ambiguously, so
// the explicit `error(...)` here pins it to `string`.
fun _bytes_to_string(bytes: uint8[]) -> string! {
    match _string_from_bytes(bytes) {
        Ok { value } => { return value }
        Err { error } => {}
    }
    return error("invalid UTF-8 byte sequence")
}

// The one-character string for byte `b` (used for control-character escapes).
fun _byte_char(b: int64) -> string! {
    let bytes: uint8[] = []
    bytes.push(_u8(b))
    return _bytes_to_string(bytes)!
}

// Encode a Unicode scalar value as its UTF-8 text.
fun _encode_utf8(cp: int64) -> string! {
    let bytes: uint8[] = []
    if cp < 128 {
        bytes.push(_u8(cp))
    } else if cp < 2048 {
        bytes.push(_u8(192 + cp / 64))
        bytes.push(_u8(128 + cp % 64))
    } else if cp < 65536 {
        bytes.push(_u8(224 + cp / 4096))
        bytes.push(_u8(128 + (cp / 64) % 64))
        bytes.push(_u8(128 + cp % 64))
    } else {
        bytes.push(_u8(240 + cp / 262144))
        bytes.push(_u8(128 + (cp / 4096) % 64))
        bytes.push(_u8(128 + (cp / 64) % 64))
        bytes.push(_u8(128 + cp % 64))
    }
    return _bytes_to_string(bytes)!
}

