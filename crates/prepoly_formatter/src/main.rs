//! `ppfmt`: the standalone formatter CLI. Prints one file's formatted text
//! to stdout; with `--write` (or `-w`), rewrites each file in place instead.
//! Exits non-zero on a syntax error (the offending file is reported and left
//! untouched).

use std::process::ExitCode;

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let write = args.first().is_some_and(|a| a == "--write" || a == "-w");
    if write {
        args.remove(0);
    }
    if args.is_empty() || (!write && args.len() != 1) {
        eprintln!("usage: ppfmt FILE | ppfmt --write|-w FILE...");
        return ExitCode::FAILURE;
    }
    let mut failed = false;
    for path in &args {
        let src = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("{path}: {e}");
                failed = true;
                continue;
            }
        };
        match prepoly_formatter::format_source(&src) {
            Ok(out) => {
                if write {
                    if out != src
                        && let Err(e) = std::fs::write(path, out)
                    {
                        eprintln!("{path}: {e}");
                        failed = true;
                    }
                } else {
                    print!("{out}");
                }
            }
            Err(errors) => {
                for e in errors {
                    let (line, col) = prepoly_parser::line_col(&src, e.span.lo);
                    eprintln!("{path}:{line}:{col}: {}", e.message);
                }
                failed = true;
            }
        }
    }
    if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
