//! Every Brass fence rendered with a Run button must remain a self-contained,
//! type-correct program. Multi-file, native-only, and intentionally incomplete
//! examples opt out with the `norun` fence flag.

use std::path::{Path, PathBuf};
use std::process::Command;

struct Example {
    source_path: PathBuf,
    line: usize,
    code: String,
}

fn collect_markdown(dir: &Path, files: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
        .expect("read book directory")
        .map(|entry| entry.expect("read book entry").path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            collect_markdown(&path, files);
        } else if matches!(
            path.extension().and_then(|ext| ext.to_str()),
            Some("md" | "mdx")
        ) {
            files.push(path);
        }
    }
}

fn fence_start(line: &str) -> Option<(u8, usize, &str)> {
    let line = line.trim_start();
    let marker = *line.as_bytes().first()?;
    if marker != b'`' && marker != b'~' {
        return None;
    }
    let count = line.bytes().take_while(|byte| *byte == marker).count();
    (count >= 3).then(|| (marker, count, line[count..].trim()))
}

fn examples_in(path: &Path) -> Vec<Example> {
    let text = std::fs::read_to_string(path).expect("read Markdown");
    let mut examples = Vec::new();
    let mut open: Option<(u8, usize, bool, usize, String)> = None;
    for (index, line) in text.lines().enumerate() {
        if let Some((marker, count, capture, start, code)) = &mut open {
            let close = fence_start(line)
                .is_some_and(|(m, n, rest)| m == *marker && n >= *count && rest.is_empty());
            if close {
                if *capture {
                    examples.push(Example {
                        source_path: path.to_path_buf(),
                        line: *start,
                        code: std::mem::take(code),
                    });
                }
                open = None;
            } else if *capture {
                code.push_str(line);
                code.push('\n');
            }
            continue;
        }
        let Some((marker, count, info)) = fence_start(line) else {
            continue;
        };
        let flags: Vec<&str> = info.split_whitespace().collect();
        let capture = flags.first() == Some(&"brass") && !flags.contains(&"norun");
        open = Some((marker, count, capture, index + 1, String::new()));
    }
    examples
}

/// A docs edit must not leave the browser's Run button attached to a snippet
/// that cannot pass the compiler. Failures identify the source fence directly.
#[test]
fn runnable_book_fences_typecheck() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../book/src/content/docs");
    let mut markdown = Vec::new();
    collect_markdown(&root, &mut markdown);
    let examples: Vec<Example> = markdown.iter().flat_map(|path| examples_in(path)).collect();
    assert!(!examples.is_empty(), "no runnable Brass fences found");

    let scratch = std::env::temp_dir().join(format!("brass_book_examples-{}", std::process::id()));
    std::fs::create_dir_all(&scratch).expect("create example directory");
    let std_packages = format!(
        "std={}",
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .display()
    );
    let mut failures = Vec::new();
    for (index, example) in examples.iter().enumerate() {
        let program = scratch.join(format!("example-{index}.cz"));
        std::fs::write(&program, &example.code).expect("write book example");
        let output = Command::new(env!("CARGO_BIN_EXE_brass"))
            .env("BRASS_CACHE", "off")
            .env("BRASS_PACKAGES", &std_packages)
            .args(["check", program.to_str().expect("UTF-8 temporary path")])
            .output()
            .expect("check book example");
        if !output.status.success() {
            failures.push(format!(
                "{}:{}\n{}",
                example.source_path.display(),
                example.line,
                String::from_utf8_lossy(&output.stderr)
            ));
        }
    }
    let _ = std::fs::remove_dir_all(&scratch);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
