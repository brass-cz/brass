//! Regular expression matching, as a native Brass plugin.
//!
//! `std/regex.cz` owns the user-facing API (the `Regex` type, `Match`,
//! `Group`) and calls in here for compilation and matching. The engine is
//! Rust's `regex`: a finite-automaton matcher with a linear-time guarantee, so
//! a pattern applied to untrusted input cannot blow up (the price is no
//! backreferences and no lookaround -- neither is expressible in an automaton).
//!
//! A compiled regex is not a value the plugin ABI can carry, so it lives in a
//! process-wide handle table and every function takes an `i64` handle -- the
//! shape the net library's TLS sessions and the hash library's streaming
//! hashers use. Unlike those, a regex is never released: a `Regex` value is
//! immutable and cheap to keep, and dropping one would need a destructor the
//! language does not have. A program that compiles regexes in a loop therefore
//! grows; compile once, outside the loop, as with any regex engine.
//!
//! Matches cross the boundary as BYTE OFFSETS into the subject string, never as
//! substrings: Brass string offsets are UTF-8 byte offsets throughout, so the
//! wrapper slices the text itself and the offsets stay meaningful to a caller
//! that wants them (`Match.start`/`end`). Offsets from this engine always fall
//! on character boundaries.

use std::sync::{Arc, OnceLock};

use brass_plugin::{BrassLib, HandleError, HandleTable, Registry, brass_lib, decl, export};
use regex::Regex;

/// The compiled regexes, by handle. Cloned out (an `Arc`) before matching, so
/// the global lock is held only for the lookup -- a long match on one regex
/// never blocks another thread's lookup.
fn table() -> &'static HandleTable<Arc<Regex>> {
    static TABLE: OnceLock<HandleTable<Arc<Regex>>> = OnceLock::new();
    TABLE.get_or_init(HandleTable::new)
}

/// The regex behind `handle`.
///
/// A handle is only ever minted by `regex_compile` and never released, and the
/// Brass `Regex` type keeps its handle private -- so an unknown handle means
/// the wrapper is broken, not that the user did anything. Panicking says that
/// (the ABI catches it and reports the call as failed) instead of making every
/// match fallible on the Brass side for an error it cannot produce.
fn regex(handle: i64) -> Arc<Regex> {
    table()
        .get_cloned(handle)
        .unwrap_or_else(|error| panic!("{}", handle_error(error)))
}

fn handle_error(error: HandleError) -> String {
    match error {
        HandleError::Poisoned => "the regex table is poisoned".to_string(),
        HandleError::Exhausted => "the regex table cannot allocate another handle".to_string(),
        HandleError::Missing(handle) => format!("regex handle {handle} does not exist"),
    }
}

/// The capture spans of `caps` as a flat `[start, end, start, end, ...]` run,
/// one pair per group in group order (group 0 is the whole match). A group that
/// did not participate in the match -- the `(a)` of `(a)|(b)` against `"b"` --
/// has no span, and is reported as `(-1, -1)` so an empty match at offset 0 is
/// still distinguishable from an absent group.
fn spans(caps: &regex::Captures<'_>, out: &mut Vec<i64>) {
    for group in caps.iter() {
        match group {
            Some(m) => {
                out.push(m.start() as i64);
                out.push(m.end() as i64);
            }
            None => {
                out.push(-1);
                out.push(-1);
            }
        }
    }
}

export! {
    /// Compile `pattern` and return its handle. The only failure: a pattern the
    /// engine rejects (bad syntax, or a construct it does not have -- a
    /// backreference, a lookaround, or a repetition whose compiled size exceeds
    /// the engine's limit).
    fn regex_compile(pattern: String) -> Result<i64, String> {
        let re = Regex::new(&pattern).map_err(|e| e.to_string())?;
        table()
            .insert(Arc::new(re))
            .map_err(handle_error)
    }

    /// The name of each capture group in group order, empty for an unnamed one
    /// (group 0, the whole match, is always unnamed). Its length is the group
    /// count, which the wrapper needs to cut `regex_find_all`'s flat span run
    /// into matches.
    fn regex_group_names(handle: i64) -> Vec<String> {
        regex(handle)
            .capture_names()
            .map(|n| n.unwrap_or("").to_string())
            .collect()
    }

    /// Whether the regex matches anywhere in `text`. Cheaper than `regex_find`:
    /// the engine stops at the first match and never records capture spans.
    fn regex_is_match(handle: i64, text: String) -> bool {
        regex(handle).is_match(&text)
    }

    /// The capture spans of the leftmost match starting at or after byte offset
    /// `from` (see [`spans`]), or an empty array when there is none.
    ///
    /// `from` is where the SEARCH starts, not where the string starts: `^` still
    /// anchors to the real beginning of `text` and a lookbehind-free pattern
    /// sees the text before `from` as context. That is what makes an
    /// iterate-from-here loop behave like `find_all`.
    fn regex_find(handle: i64, text: String, from: i64) -> Vec<i64> {
        let re = regex(handle);
        let from = from.clamp(0, text.len() as i64) as usize;
        let mut out = Vec::new();
        // A `from` that lands inside a multi-byte character cannot start a
        // match; the engine would panic on it, so report "no match" instead.
        if !text.is_char_boundary(from) {
            return out;
        }
        if let Some(caps) = re.captures_at(&text, from) {
            spans(&caps, &mut out);
        }
        out
    }

    /// The capture spans of every non-overlapping match, leftmost-first: the
    /// per-match runs of [`spans`] concatenated. The wrapper cuts them apart by
    /// the group count (`regex_group_names`), so the flat shape costs nothing.
    fn regex_find_all(handle: i64, text: String) -> Vec<i64> {
        let re = regex(handle);
        let mut out = Vec::new();
        for caps in re.captures_iter(&text) {
            spans(&caps, &mut out);
        }
        out
    }

    /// `text` with the first `limit` matches replaced by `replacement` (all of
    /// them when `limit` is 0 or negative). `replacement` expands `$1` / `$name`
    /// / `${1}` to that capture group's text and `$$` to a literal `$`; a name
    /// that no group has expands to the empty string.
    fn regex_replace(handle: i64, text: String, replacement: String, limit: i64) -> String {
        let re = regex(handle);
        let limit = if limit <= 0 { 0 } else { limit as usize };
        re.replacen(&text, limit, replacement.as_str()).into_owned()
    }

    /// `text` split around every match, in order. Adjacent matches and a match
    /// at either end yield empty fields (as `string.split` does), so the field
    /// count is always one more than the match count.
    fn regex_split(handle: i64, text: String) -> Vec<String> {
        regex(handle)
            .split(&text)
            .map(str::to_string)
            .collect()
    }

    /// `text` with every regex metacharacter escaped, so the result matches it
    /// literally. Use it to build a pattern around text the program did not
    /// write (a user's search term).
    fn regex_escape(text: String) -> String {
        regex::escape(&text)
    }
}

struct RegexLib;

impl BrassLib for RegexLib {
    fn entry(reg: &mut Registry) {
        reg.export(decl!(regex_compile));
        reg.export(decl!(regex_group_names));
        reg.export(decl!(regex_is_match));
        reg.export(decl!(regex_find));
        reg.export(decl!(regex_find_all));
        reg.export(decl!(regex_replace));
        reg.export(decl!(regex_split));
        reg.export(decl!(regex_escape));
    }
}

brass_lib!(RegexLib);

#[cfg(test)]
mod tests {
    use super::*;

    fn compile(pattern: &str) -> i64 {
        let re = Regex::new(pattern).expect("valid pattern");
        table().insert(Arc::new(re)).expect("insert regex")
    }

    /// A non-participating group is `(-1, -1)`, not an empty span at 0: the
    /// wrapper turns the former into `null` and the latter into an empty group,
    /// and confusing them would make `(a)|(b)` report a match for the wrong arm.
    #[test]
    fn absent_group_is_minus_one() {
        let h = compile(r"(a)|(b)");
        let re = regex(h);
        let caps = re.captures("b").expect("matches");
        let mut out = Vec::new();
        spans(&caps, &mut out);
        assert_eq!(out, vec![0, 1, -1, -1, 0, 1]);
    }

    /// The search offset is where the search STARTS, not a substring boundary:
    /// the reported spans are still absolute offsets into the whole text.
    #[test]
    fn find_from_reports_absolute_offsets() {
        let h = compile(r"\d+");
        let re = regex(h);
        let caps = re.captures_at("a1 b22", 2).expect("matches");
        let m = caps.get(0).unwrap();
        assert_eq!((m.start(), m.end()), (4, 6));
    }

    /// A search offset inside a multi-byte character must not reach the engine
    /// (it panics there); the export reports "no match" instead.
    #[test]
    fn a_non_boundary_offset_is_not_a_match() {
        let h = compile(r".");
        let text = "é";
        assert!(!text.is_char_boundary(1), "the test text is multi-byte");
        let re = regex(h);
        assert!(text.is_char_boundary(0) && re.captures_at(text, 0).is_some());
    }
}
