//! The fixture plugin the workspace tests load: one function per supported
//! parameter/return shape, plus a fallible one and an undocumented one.

use prepoly_plugin::{Bytes, PrepolyLib, Registry, decl, export, prepoly_lib};

export! {
    /// Adds two integers.
    fn add(a: i64, b: i64) -> i64 { a.wrapping_add(b) }

    /// Repeats `text` `times` times, separated by spaces.
    fn repeat(text: String, times: i64) -> String {
        let times = usize::try_from(times).unwrap_or(0);
        vec![text; times].join(" ")
    }

    /// Divides `a` by `b`, failing on a zero divisor.
    fn checked_div(a: i64, b: i64) -> Result<i64, String> {
        if b == 0 {
            Err("division by zero".to_string())
        } else {
            Ok(a / b)
        }
    }

    /// The byte count of `data`.
    fn byte_len(data: Bytes) -> i64 { data.len() as i64 }

    /// Joins `parts` with `sep`.
    fn join(parts: Vec<String>, sep: String) -> String { parts.join(&sep) }

    /// Splits `text` on `sep`, returning the pieces.
    fn split(text: String, sep: String) -> Vec<String> {
        text.split(&sep).map(str::to_string).collect()
    }

    /// The length of each row of `rows`.
    fn row_lengths(rows: Vec<Vec<String>>) -> Vec<i64> {
        rows.iter().map(|r| r.len() as i64).collect()
    }

    /// Scales `x` by `factor`.
    fn scale(x: f64, factor: f64) -> f64 { x * factor }

    /// Whether `v` is even.
    fn is_even(v: i64) -> bool { v % 2 == 0 }

    fn undocumented() {}
}

struct TestLib;

impl PrepolyLib for TestLib {
    fn entry(reg: &mut Registry) {
        reg.export(decl!(add));
        reg.export(decl!(repeat));
        reg.export(decl!(checked_div));
        reg.export(decl!(byte_len));
        reg.export(decl!(join));
        reg.export(decl!(split));
        reg.export(decl!(row_lengths));
        reg.export(decl!(scale));
        reg.export(decl!(is_even));
        reg.export(decl!(undocumented));
    }
}

prepoly_lib!(TestLib);
