//! Source formatter for Prepoly.
//!
//! Formats a whole source file by re-printing its AST. Comments and string /
//! numeric literals are re-read verbatim from the original source (the lexer
//! resolves escapes and radix prefixes, so the AST alone cannot reproduce
//! them); blank lines between elements are preserved, collapsed to one.
//!
//! Layout: 4-space indentation and an 80-column target width. Block constructs
//! (`fun`, `if`, `while`, `for`, `match`) always put their bodies on indented
//! lines; expressions that overflow the width break by construct-specific
//! rules -- see the `expr` module docs.
//!
//! A comment that sits *inside* a construct the formatter renders flat (for
//! example between two call arguments that end up on one line) is moved to
//! just after that construct rather than dropped.

mod comments;
mod expr;
mod printer;

pub use printer::{INDENT, MAX_WIDTH};

use prepoly_parser::ParseError;

/// Format `src`, returning the formatted text or the file's syntax errors.
/// A file that does not parse is never rewritten: the recovered AST drops the
/// broken constructs, so printing it would lose code.
pub fn format_source(src: &str) -> Result<String, Vec<ParseError>> {
    let (module, errors) = prepoly_parser::parse_recovering(src, 0);
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(printer::print_module(src, &module))
}

#[cfg(test)]
mod tests {
    use super::format_source;

    fn fmt(src: &str) -> String {
        format_source(src).unwrap_or_else(|e| panic!("parse errors: {e:?}"))
    }

    /// Formatting must produce parseable output and be idempotent.
    fn roundtrip(src: &str) -> String {
        let once = fmt(src);
        let twice = format_source(&once)
            .unwrap_or_else(|e| panic!("formatted output failed to parse: {e:?}\n---\n{once}"));
        assert_eq!(once, twice, "formatting is not idempotent");
        once
    }

    #[test]
    fn normalizes_indentation_and_spacing() {
        let src = "fun main()   {\n  let x=1+2\n        println( x )\n}\n";
        assert_eq!(
            roundtrip(src),
            "fun main() {\n    let x = 1 + 2\n    println(x)\n}\n"
        );
    }

    /// A `for` loop variable is a pattern, so a destructuring one round-trips as
    /// written rather than decaying to a name.
    #[test]
    fn for_destructuring_pattern_round_trips() {
        let src = "fun main(){for [ k,v ] in m.pairs(){println(k)}}";
        assert_eq!(
            roundtrip(src),
            "fun main() {\n    for [k, v] in m.pairs() {\n        println(k)\n    }\n}\n"
        );
    }

    #[test]
    fn if_blocks_always_break() {
        let src = "fun f(a: int32) -> int32 { if a > 0 { return a } else { return -a } }";
        assert_eq!(
            roundtrip(src),
            "fun f(a: int32) -> int32 {\n    if a > 0 {\n        return a\n    } else {\n        return -a\n    }\n}\n"
        );
    }

    #[test]
    fn long_method_chain_breaks_every_segment() {
        let src = "fun main() {\n    let result = collection_of_values.filter((x) -> x > 0).map((x) -> x * 2).sum()\n}\n";
        assert_eq!(
            roundtrip(src),
            "fun main() {\n    let result = collection_of_values\n        .filter((x) -> x > 0)\n        .map((x) -> x * 2)\n        .sum()\n}\n"
        );
    }

    #[test]
    fn short_method_chain_stays_flat() {
        let src = "fun main() {\n    let r = xs.map(f).sum()\n}\n";
        assert_eq!(
            roundtrip(src),
            "fun main() {\n    let r = xs.map(f).sum()\n}\n"
        );
    }

    #[test]
    fn long_array_breaks_one_element_per_line() {
        let src = "fun main() {\n    let a = [aaaaaaaaaaa, bbbbbbbbbbb, ccccccccccc, ddddddddddd, eeeeeeeeeee, fffffffffff]\n}\n";
        assert_eq!(
            roundtrip(src),
            "fun main() {\n    let a = [\n        aaaaaaaaaaa,\n        bbbbbbbbbbb,\n        ccccccccccc,\n        ddddddddddd,\n        eeeeeeeeeee,\n        fffffffffff,\n    ]\n}\n"
        );
    }

    #[test]
    fn width_eighty_exactly_stays_flat() {
        // 4 + 76 characters: the limit is "no more than 80", inclusive. One
        // character more (see below) and the same call breaks.
        let src = "fun main() {\n    configure(first_option, second_option, third_option, fourth_option, xyzwvuq)\n}\n";
        assert_eq!(
            roundtrip(src),
            "fun main() {\n    configure(first_option, second_option, third_option, fourth_option, xyzwvuq)\n}\n"
        );
    }

    #[test]
    fn long_call_breaks_after_the_paren() {
        // One character past the width the flat form above fits in exactly.
        let src = "fun main() {\n    configure(first_option, second_option, third_option, fourth_option, xyzwvuqr)\n}\n";
        assert_eq!(
            roundtrip(src),
            "fun main() {\n    configure(\n        first_option,\n        second_option,\n        third_option,\n        fourth_option,\n        xyzwvuqr,\n    )\n}\n"
        );
    }

    #[test]
    fn grouping_parens_follow_precedence() {
        // Needed parens survive; redundant ones are dropped.
        let src = "fun main() {\n    let x = ((a + b)) * c\n    let y = (a * b) + c\n    let z = a - (b - c)\n}\n";
        assert_eq!(
            roundtrip(src),
            "fun main() {\n    let x = (a + b) * c\n    let y = a * b + c\n    let z = a - (b - c)\n}\n"
        );
    }

    #[test]
    fn head_position_type_literal_keeps_parens() {
        // In an `if` head a bare `Name { .. }` would be read as the block.
        let src = "fun f(p: Point) -> bool {\n    if p == (Point { x: 1 }) {\n        return true\n    }\n    return false\n}\n";
        let out = roundtrip(src);
        assert!(
            out.contains("if p == (Point { x: 1 }) {"),
            "parens dropped in head position:\n{out}"
        );
    }

    #[test]
    fn comments_are_preserved() {
        let src = "// header\n\nfun main() {\n    // before\n    let x = 1 // trailing\n\n    /* block */\n    let y = 2\n}\n// tail\n";
        assert_eq!(
            roundtrip(src),
            "// header\n\nfun main() {\n    // before\n    let x = 1 // trailing\n\n    /* block */\n    let y = 2\n}\n// tail\n"
        );
    }

    // `#` comments survive formatting like `//` ones, and a shebang stays on
    // the first line.
    #[test]
    fn hash_comments_and_shebang_are_preserved() {
        let src =
            "#!/usr/bin/env prepoly\n\nfun main() {\n    # before\n    let x = 1 # trailing\n}\n";
        assert_eq!(
            roundtrip(src),
            "#!/usr/bin/env prepoly\n\nfun main() {\n    # before\n    let x = 1 # trailing\n}\n"
        );
    }

    #[test]
    fn blank_lines_collapse_to_one() {
        let src = "fun a() {\n}\n\n\n\nfun b() {\n}\n";
        assert_eq!(roundtrip(src), "fun a() {\n}\n\nfun b() {\n}\n");
    }

    #[test]
    fn literals_keep_their_spelling() {
        let src = "fun main() {\n    let a = 0xFF\n    let b = 1_000_000\n    let c = 1.0e-5\n    let s = \"tab\\t{a + b} \\{raw}\"\n}\n";
        let out = roundtrip(src);
        assert!(out.contains("0xFF"), "{out}");
        assert!(out.contains("1_000_000"), "{out}");
        assert!(out.contains("1.0e-5"), "{out}");
        assert!(out.contains("\"tab\\t{a + b} \\{raw}\""), "{out}");
    }

    #[test]
    fn match_arms_get_trailing_commas_and_keep_sugar() {
        let src = "fun f(s, n) {\n    match s {\n        Circle { radius } => radius\n        Point => n += 1\n        _ => 0\n    }\n}\n";
        assert_eq!(
            roundtrip(src),
            "fun f(s, n) {\n    match s {\n        Circle { radius } => radius,\n        Point => n += 1,\n        _ => 0,\n    }\n}\n"
        );
    }

    #[test]
    fn rest_pattern_is_preserved() {
        let src = "fun f(s) {\n    if let Circle { radius, .. } = s {\n        return radius\n    }\n    return 0\n}\n";
        let out = roundtrip(src);
        assert!(out.contains("Circle { radius, .. }"), "{out}");
    }

    #[test]
    fn sum_type_layout() {
        // Short sums inline; long ones get one leading-pipe line per variant.
        let short = "type Color = Red | Green | Blue\n";
        assert_eq!(roundtrip(short), "type Color = Red | Green | Blue\n");
        let single = "type Wrap =\n    | Only { value: int32 }\n";
        assert_eq!(roundtrip(single), "type Wrap = | Only { value: int32 }\n");
        let long = "type Shape = Circle { radius: float64 } | Rectangle { width: float64, height: float64 }\n";
        assert_eq!(
            roundtrip(long),
            "type Shape =\n    | Circle { radius: float64 }\n    | Rectangle { width: float64, height: float64 }\n"
        );
    }

    #[test]
    fn record_type_and_refinement_alias() {
        let src = "type StringCount = HashMap { key: string, value: int32 }\ntype P = {\n    x: float64\n    dist(self, o: P) -> float64\n}\n";
        assert_eq!(
            roundtrip(src),
            "type StringCount = HashMap { key: string, value: int32 }\ntype P = {\n    x: float64\n    dist(self, o: P) -> float64\n}\n"
        );
    }

    #[test]
    fn long_binary_chain_breaks_after_operators() {
        let src = "fun main() {\n    let ok = first_condition && second_condition && third_condition && fourth_condition\n}\n";
        assert_eq!(
            roundtrip(src),
            "fun main() {\n    let ok = first_condition &&\n        second_condition &&\n        third_condition &&\n        fourth_condition\n}\n"
        );
    }

    #[test]
    fn imports_break_when_long() {
        let src =
            "import some.very.long.module.path.{ FirstName, SecondName, ThirdName, FourthName }\n";
        assert_eq!(
            roundtrip(src),
            "import some.very.long.module.path.{\n    FirstName,\n    SecondName,\n    ThirdName,\n    FourthName,\n}\n"
        );
    }

    #[test]
    fn overlong_signature_breaks_parameters() {
        let src = "fun configure(first_option: int32, second_option: int32, third: int32) -> int32 {\n    return third\n}\n";
        assert_eq!(
            roundtrip(src),
            "fun configure(\n    first_option: int32,\n    second_option: int32,\n    third: int32,\n) -> int32 {\n    return third\n}\n"
        );
    }

    #[test]
    fn syntax_errors_refuse_to_format() {
        assert!(format_source("fun f() {\n    let x = )\n}\n").is_err());
    }

    #[test]
    fn closure_with_block_body() {
        let src = "fun main() {\n    let g = () -> { return 1 }\n}\n";
        assert_eq!(
            roundtrip(src),
            "fun main() {\n    let g = () -> {\n        return 1\n    }\n}\n"
        );
    }

    #[test]
    fn nested_break_inside_broken_args() {
        // An argument that cannot fit breaks recursively inside the arg list:
        // `compute(..)` overflows even at the indent the outer break gives it.
        let src = "fun main() {\n    register(compute(alpha_value, beta_value, gamma_value, delta_value, epsilon_value), name)\n}\n";
        assert_eq!(
            roundtrip(src),
            "fun main() {\n    register(\n        compute(\n            alpha_value,\n            beta_value,\n            gamma_value,\n            delta_value,\n            epsilon_value,\n        ),\n        name,\n    )\n}\n"
        );
    }
}
