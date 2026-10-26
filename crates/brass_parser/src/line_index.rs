//! Indexed source coordinates for human-facing diagnostics.

/// LF line boundaries for repeated scalar-column queries on one source text.
/// Columns follow [`crate::line_col`], not display widths or UTF-16 positions.
pub struct LineIndex {
    line_starts: Vec<usize>,
}

impl LineIndex {
    /// Index every line start, including the empty line after a trailing LF.
    pub fn new(src: &str) -> Self {
        Self {
            line_starts: std::iter::once(0)
                .chain(
                    src.bytes()
                        .enumerate()
                        .filter_map(|(i, byte)| (byte == b'\n').then_some(i + 1)),
                )
                .collect(),
        }
    }

    /// Return the one-based line and Unicode scalar column in the indexed text.
    /// `src` must be the same text passed to [`Self::new`]. Offsets inside a
    /// scalar count that scalar; offsets beyond EOF return the EOF position.
    pub fn line_col(&self, src: &str, byte_offset: usize) -> (usize, usize) {
        let offset = byte_offset.min(src.len());
        let line = self.line_starts.partition_point(|&start| start <= offset) - 1;
        let start = self.line_starts[line];
        // Only the line start is a guaranteed UTF-8 boundary. Counting scalar
        // starts preserves the one-shot API's behavior inside a scalar.
        let column = src[start..]
            .char_indices()
            .take_while(|&(i, _)| i < offset - start)
            .count();
        (line + 1, column + 1)
    }
}

#[cfg(test)]
mod tests {
    use super::LineIndex;

    fn assert_coordinates(src: &str) {
        let index = LineIndex::new(src);
        for offset in (0..=src.len() + 2).chain(std::iter::once(usize::MAX)) {
            assert_eq!(
                index.line_col(src, offset),
                crate::line_col(src, offset),
                "source {src:?}, offset {offset}"
            );
        }
    }

    #[test]
    fn scalar_coordinates_match_one_shot_at_every_byte() {
        // Interior UTF-8 offsets, CRLF, lone CR and combining marks exercise
        // the distinctions from byte columns and LSP coordinates.
        let alphabet = [
            'a',
            '\n',
            '\r',
            '\t',
            '\u{e9}',
            '\u{4e2d}',
            '\u{1f600}',
            '\u{301}',
        ];
        assert_coordinates("");
        for a in alphabet {
            for b in alphabet {
                for c in alphabet {
                    assert_coordinates(&format!("{a}{b}{c}"));
                }
            }
        }
        assert_coordinates("a\r\nb\rc\n\n\t\u{1f600}e\u{301}\u{4e2d}\u{e9}\n");
    }

    #[test]
    fn long_lines_and_many_empty_lines_match_one_shot() {
        // Binary search must select the same line at LF, just after LF and EOF.
        assert_coordinates(&format!("{}\n{}", "\u{e9}\t".repeat(256), "\n".repeat(256)));
    }
}
