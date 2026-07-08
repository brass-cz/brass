// JSON: a value tree, a recursive-descent parser, accessors, a serializer, and
// a reflective decoder into typed structures. Part of the standard library but
// NOT in the implicit prelude -- import it explicitly:
//
//     import std.data.json.{ JsonValue, parse }
//
// The value tree mirrors the six JSON kinds. An Object keeps its members as
// parallel `keys`/`vals` arrays rather than a `HashMap`: the typed back end
// cannot lay a `HashMap` out inside a sum variant, and object field counts are
// small, so an association list is the practical representation here (a
// `HashMap` remains available to user code via `import std.collections`).

/**
 * A parsed JSON value, one variant per JSON kind. Obtain one with `parse`,
 * inspect it with the accessors (`get`, `at`, `as_*`), decode it into a typed
 * structure with `into`, and render it back to text with `stringify`.
 */
type JsonValue =
    | Null
    | Bool { value: bool }
    | Number { value: float64 }
    | String { value: string }
    | Array { value: JsonValue[] }
    | Object { keys: string[], vals: JsonValue[] }

// ----- accessors -----

/** The boolean inside a `Bool`, or an error for any other kind. */
fun JsonValue.as_bool(self) -> bool! {
    match self {
        JsonValue.Bool { value } => { return value }
        _ => {}
    }
    return error("expected a JSON boolean")
}

/** The number inside a `Number`, or an error for any other kind. */
fun JsonValue.as_number(self) -> float64! {
    match self {
        JsonValue.Number { value } => { return value }
        _ => {}
    }
    return error("expected a JSON number")
}

/** The string inside a `String`, or an error for any other kind. */
fun JsonValue.as_string(self) -> string! {
    match self {
        JsonValue.String { value } => { return value }
        _ => {}
    }
    return error("expected a JSON string")
}

/** Whether this value is JSON `null`. */
fun JsonValue.is_null(self) -> bool {
    match self {
        JsonValue.Null => { return true }
        _ => {}
    }
    return false
}

/** The value of object field `key`, or an error naming the missing field. */
fun JsonValue.get(self, key: string) -> JsonValue! {
    match self {
        JsonValue.Object { keys, vals } => {
            for i in [0..keys.len()] {
                if keys[i] == key {
                    return vals[i]
                }
            }
            return error("missing field '{key}'")
        }
        _ => {}
    }
    return error("expected a JSON object")
}

/** The element at `index` of an array, or an error when out of range. */
fun JsonValue.at(self, index: int64) -> JsonValue! {
    match self {
        JsonValue.Array { value } => {
            if index >= 0 && index < len(value) {
                return value[index]
            }
            return error("array index {index} out of range")
        }
        _ => {}
    }
    return error("expected a JSON array")
}

// ----- reflective decoding -----

/**
 * Decode `self` into the type the call site expects, driven entirely by that
 * target type: `const u: User = j.into()!`. A scalar target reads the
 * matching JSON scalar; a record target walks its own fields (each decoded
 * recursively); a nullable target accepts JSON null. A JSON value of the
 * wrong kind for the target is a runtime decode error.
 */
fun JsonValue.into(self) -> infer! {
    match self {
        JsonValue.Number { value } => { return infer.from(value) }
        JsonValue.String { value } => { return infer.from(value) }
        JsonValue.Bool { value } => { return infer.from(value) }
        JsonValue.Null => { return null }
        JsonValue.Object { keys, vals } => {
            let ret: infer
            for field in fields(ret) {
                ret[field] = self.get(field)!.into()!
            }
            return ret
        }
        JsonValue.Array { value } => {
            return error("cannot decode a JSON array into a scalar or record")
        }
    }
}

// ----- serialization -----
//
// A free function, not a method, on purpose: the checker's per-call
// re-elaboration currently does not converge for a SELF-RECURSIVE method over a
// sum with six or more variants (a free function recurses fine), so `stringify`
// is called as `stringify(value)` rather than `value.stringify()`.

/** Render a `JsonValue` back to compact JSON text (no added whitespace). */
fun stringify(value: JsonValue) -> string {
    match value {
        JsonValue.Null => { return "null" }
        JsonValue.Bool { value } => {
            if value { return "true" }
            return "false"
        }
        JsonValue.Number { value } => { return "{value}" }
        JsonValue.String { value } => { return _quote(value) }
        JsonValue.Array { value } => {
            let out = "["
            let first = true
            for elem in value {
                if !first { out = out + "," }
                out = out + stringify(elem)
                first = false
            }
            return out + "]"
        }
        JsonValue.Object { keys, vals } => {
            let out = "\{"
            for i in [0..keys.len()] {
                if i > 0 { out = out + "," }
                out = out + _quote(keys[i]) + ":" + stringify(vals[i])
            }
            return out + "\}"
        }
    }
}

// Wrap a string in double quotes with the JSON escapes the parser accepts.
// Iterated by byte index rather than `s.chars()` on purpose: the checker's
// per-call re-elaboration does not converge when a recursive method
// (`stringify`) calls a helper that in turn builds an inferred `[]` array (as
// `chars` does), so this stays index-based.
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
// current byte offset; its methods advance it. `parse` requires the whole input
// to be one JSON value (trailing content is an error).

type _Cursor = {
    text: string
    pos: int64
}

/**
 * Parse `text` as one JSON value. The whole input must be consumed: trailing
 * content is an error.
 */
fun parse(text: string) -> JsonValue! {
    let cur = _Cursor { text: text, pos: 0 }
    cur._skip_ws()
    const value = cur._value()!
    cur._skip_ws()
    if cur.pos != len(cur.text) {
        return error("unexpected trailing characters at offset {cur.pos}")
    }
    return value
}

fun _Cursor._peek(self) -> string {
    if self.pos >= len(self.text) {
        return ""
    }
    if let c = _string_char_at(self.text, self.pos) {
        return c
    }
    return ""
}

fun _Cursor._skip_ws(self) {
    while self.pos < len(self.text) {
        const c = self._peek()
        if c == " " || c == "\n" || c == "\t" || c == "\r" {
            self.pos = self.pos + 1
        } else {
            return
        }
    }
}

fun _Cursor._value(self) -> JsonValue! {
    const c = self._peek()
    if c == "\{" {
        return self._object()!
    }
    if c == "[" {
        return self._array()!
    }
    if c == "\"" {
        return JsonValue.String { value: self._string()! }
    }
    if c == "t" || c == "f" {
        return self._bool()!
    }
    if c == "n" {
        return self._null()!
    }
    return self._number()
}

fun _Cursor._object(self) -> JsonValue! {
    self.pos = self.pos + 1
    let keys: string[] = []
    let vals: JsonValue[] = []
    self._skip_ws()
    if self._peek() == "\}" {
        self.pos = self.pos + 1
        return JsonValue.Object { keys: keys, vals: vals }
    }
    while true {
        self._skip_ws()
        const key = self._string()!
        self._skip_ws()
        if self._peek() != ":" {
            return error("expected ':' in object at offset {self.pos}")
        }
        self.pos = self.pos + 1
        self._skip_ws()
        const val = self._value()!
        keys.push(key)
        vals.push(val)
        self._skip_ws()
        const sep = self._peek()
        self.pos = self.pos + 1
        if sep == "\}" {
            return JsonValue.Object { keys: keys, vals: vals }
        }
        if sep != "," {
            return error("expected ',' or '\}' in object at offset {self.pos}")
        }
    }
    return error("unterminated object")
}

fun _Cursor._array(self) -> JsonValue! {
    self.pos = self.pos + 1
    let items: JsonValue[] = []
    self._skip_ws()
    if self._peek() == "]" {
        self.pos = self.pos + 1
        return JsonValue.Array { value: items }
    }
    while true {
        self._skip_ws()
        const val = self._value()!
        items.push(val)
        self._skip_ws()
        const sep = self._peek()
        self.pos = self.pos + 1
        if sep == "]" {
            return JsonValue.Array { value: items }
        }
        if sep != "," {
            return error("expected ',' or ']' in array at offset {self.pos}")
        }
    }
    return error("unterminated array")
}

fun _Cursor._string(self) -> string! {
    if self._peek() != "\"" {
        return error("expected a string at offset {self.pos}")
    }
    self.pos = self.pos + 1
    let out = ""
    while self.pos < len(self.text) {
        const c = self._peek()
        self.pos = self.pos + 1
        if c == "\"" {
            return out
        }
        if c == "\\" {
            const esc = self._peek()
            self.pos = self.pos + 1
            if esc == "\"" {
                out = out + "\""
            } else if esc == "\\" {
                out = out + "\\"
            } else if esc == "/" {
                out = out + "/"
            } else if esc == "n" {
                out = out + "\n"
            } else if esc == "t" {
                out = out + "\t"
            } else if esc == "r" {
                out = out + "\r"
            } else {
                return error("invalid escape in string at offset {self.pos}")
            }
        } else {
            out = out + c
        }
    }
    return error("unterminated string")
}

fun _Cursor._number(self) -> JsonValue! {
    const start = self.pos
    while self.pos < len(self.text) {
        const c = self._peek()
        if _is_number_char(c) {
            self.pos = self.pos + 1
        } else {
            return JsonValue.Number { value: float64.parse(_string_slice(self.text, start, self.pos))! }
        }
    }
    return JsonValue.Number { value: float64.parse(_string_slice(self.text, start, self.pos))! }
}

fun _is_number_char(c: string) -> bool {
    return c == "-" || c == "+" || c == "." || c == "e" || c == "E" ||
        c == "0" || c == "1" || c == "2" || c == "3" || c == "4" ||
        c == "5" || c == "6" || c == "7" || c == "8" || c == "9"
}

fun _Cursor._bool(self) -> JsonValue! {
    if _string_slice(self.text, self.pos, _min(self.pos + 4, len(self.text))) == "true" {
        self.pos = self.pos + 4
        return JsonValue.Bool { value: true }
    }
    if _string_slice(self.text, self.pos, _min(self.pos + 5, len(self.text))) == "false" {
        self.pos = self.pos + 5
        return JsonValue.Bool { value: false }
    }
    return error("invalid literal at offset {self.pos}")
}

fun _Cursor._null(self) -> JsonValue! {
    if _string_slice(self.text, self.pos, _min(self.pos + 4, len(self.text))) == "null" {
        self.pos = self.pos + 4
        return JsonValue.Null
    }
    return error("invalid literal at offset {self.pos}")
}

fun _min(a: int64, b: int64) -> int64 {
    if a < b {
        return a
    }
    return b
}
