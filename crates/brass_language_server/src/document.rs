//! In-memory document model: source text plus a line index that converts
//! between the byte-offset spans the compiler produces and the line/column
//! positions the LSP protocol speaks.
//!
//! LSP `Position` columns are UTF-16 code units (the protocol default), which
//! differ from both byte offsets and `char` counts, so the conversions here own
//! that encoding rather than reusing `brass_parser::line_col` (which counts
//! Unicode scalar values for human-facing diagnostics).

use brass_parser::Span;
use tower_lsp_server::ls_types::{Position, Range};

/// A source document and a precomputed index of its line boundaries.
pub struct Document {
    pub text: String,
    /// Byte offset at which each 0-based line begins; always starts with `0`.
    line_starts: Vec<usize>,
    /// Client-reported version, bumped on every change. Used to tag published
    /// diagnostics and to invalidate the cached full analysis.
    pub version: i32,
}

impl Document {
    pub fn new(text: String, version: i32) -> Self {
        let line_starts = line_starts(&text);
        Document {
            text,
            line_starts,
            version,
        }
    }

    pub fn update(&mut self, text: String, version: i32) {
        self.line_starts = line_starts(&text);
        self.text = text;
        self.version = version;
    }

    /// Byte offset -> LSP position. The column is the number of UTF-16 code
    /// units between the line start and `offset`.
    pub fn position_at(&self, offset: usize) -> Position {
        let offset = char_boundary_at_or_before(&self.text, offset.min(self.text.len()));
        let line = match self.line_starts.binary_search(&offset) {
            Ok(line) => line,
            Err(next) => next - 1,
        };
        let line_start = self.line_starts[line];
        let column_end = line_content_end(&self.text, line_start, offset);
        let character = self.text[line_start..column_end]
            .chars()
            .map(|c| c.len_utf16() as u32)
            .sum();
        Position {
            line: line as u32,
            character,
        }
    }

    /// LSP position -> byte offset. Out-of-range lines and columns clamp to the
    /// nearest valid offset so a stale position never panics.
    pub fn offset_at(&self, pos: Position) -> usize {
        let line = pos.line as usize;
        let Some(&line_start) = self.line_starts.get(line) else {
            return self.text.len();
        };
        let line_end = self
            .line_starts
            .get(line + 1)
            .copied()
            .unwrap_or(self.text.len());
        let line_end = line_content_end(&self.text, line_start, line_end);
        let mut remaining = pos.character;
        let mut offset = line_start;
        for c in self.text[line_start..line_end].chars() {
            let w = c.len_utf16() as u32;
            if w > remaining {
                break;
            }
            remaining -= w;
            offset += c.len_utf8();
        }
        offset
    }

    pub fn range_of(&self, span: Span) -> Range {
        Range {
            start: self.position_at(span.lo),
            end: self.position_at(span.hi),
        }
    }
}

/// A standalone line index for an arbitrary source string, used to map spans in
/// files other than the active document (e.g. a go-to-definition target in an
/// imported file) without constructing a full `Document`.
pub struct LineIndex {
    line_starts: Vec<usize>,
    len: usize,
}

impl LineIndex {
    pub fn new(text: &str) -> Self {
        LineIndex {
            line_starts: line_starts(text),
            len: text.len(),
        }
    }

    pub fn position_at(&self, text: &str, offset: usize) -> Position {
        let offset = char_boundary_at_or_before(text, offset.min(self.len).min(text.len()));
        let line = match self.line_starts.binary_search(&offset) {
            Ok(line) => line,
            Err(next) => next - 1,
        };
        let line_start = self.line_starts[line];
        let column_end = line_content_end(text, line_start, offset);
        let character = text[line_start..column_end]
            .chars()
            .map(|c| c.len_utf16() as u32)
            .sum();
        Position {
            line: line as u32,
            character,
        }
    }

    pub fn range_of(&self, text: &str, lo: usize, hi: usize) -> Range {
        Range {
            start: self.position_at(text, lo),
            end: self.position_at(text, hi),
        }
    }
}

fn line_starts(text: &str) -> Vec<usize> {
    let mut starts = vec![0];
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'\r' if bytes.get(i + 1) == Some(&b'\n') => {
                starts.push(i + 2);
                i += 2;
            }
            b'\r' | b'\n' => {
                starts.push(i + 1);
                i += 1;
            }
            _ => i += 1,
        }
    }
    starts
}

fn char_boundary_at_or_before(text: &str, mut offset: usize) -> usize {
    while !text.is_char_boundary(offset) {
        offset -= 1;
    }
    offset
}

/// Exclude a line's `\n`, `\r\n`, or lone `\r` terminator from its LSP column
/// space.
fn line_content_end(text: &str, line_start: usize, offset: usize) -> usize {
    let bytes = text.as_bytes();
    let mut end = offset;
    if end > line_start && bytes.get(end - 1) == Some(&b'\n') {
        end -= 1;
        if end > line_start && bytes.get(end - 1) == Some(&b'\r') {
            end -= 1;
        }
    } else if end > line_start && bytes.get(end - 1) == Some(&b'\r') {
        end -= 1;
    }
    end
}

#[cfg(test)]
mod tests {
    use super::Document;
    use tower_lsp_server::ls_types::Position;

    /// Out-of-range columns stop before the line terminator, and UTF-16 counts
    /// a supplementary character as two code units.
    #[test]
    fn positions_clamp_to_crlf_line_content() {
        let doc = Document::new("a😀b\r\nnext".to_string(), 1);
        assert_eq!(doc.offset_at(Position::new(0, u32::MAX)), "a😀b".len());
        assert_eq!(doc.position_at("a😀b\r".len()), Position::new(0, 4));
    }

    /// A defensive conversion of an interior UTF-8 byte offset rounds down to
    /// the preceding character boundary instead of slicing invalid text.
    #[test]
    fn interior_utf8_offsets_round_down() {
        let doc = Document::new("a😀b".to_string(), 1);
        assert_eq!(doc.position_at(2), Position::new(0, 1));
    }

    /// A lone carriage return is a line boundary of its own, so the byte after
    /// it cannot collapse onto the terminator's position on the previous line.
    #[test]
    fn lone_cr_offsets_start_a_distinct_line() {
        let doc = Document::new("first\rsecond\rthird".to_string(), 1);
        assert_eq!(doc.position_at("first".len()), Position::new(0, 5));
        assert_eq!(doc.position_at("first\r".len()), Position::new(1, 0));
        assert_eq!(doc.offset_at(Position::new(1, 3)), "first\rsec".len());
        assert_eq!(doc.offset_at(Position::new(2, 0)), "first\rsecond\r".len());
    }
}
