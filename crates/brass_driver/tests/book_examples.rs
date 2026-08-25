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

struct OpenFence {
    marker: u8,
    count: usize,
    capture: bool,
    start: usize,
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
    let mut open = Vec::<OpenFence>::new();
    for (index, line) in text.lines().enumerate() {
        if let Some(current) = open.last() {
            let close = fence_start(line).is_some_and(|(m, n, rest)| {
                m == current.marker && n >= current.count && rest.is_empty()
            });
            if close {
                let finished = open.pop().expect("open fence");
                if finished.capture {
                    examples.push(Example {
                        source_path: path.to_path_buf(),
                        line: finished.start,
                        code: finished.code,
                    });
                }
                continue;
            }
            if current.capture {
                let current = open.last_mut().expect("open fence");
                current.code.push_str(line);
                current.code.push('\n');
                continue;
            }
        }
        let Some((marker, count, info)) = fence_start(line) else {
            continue;
        };
        let flags: Vec<&str> = info.split_whitespace().collect();
        let capture = flags.first() == Some(&"brass") && !flags.contains(&"norun");
        // A four-backtick Markdown prompt can contain ordinary three-backtick
        // examples. Keep a stack so those nested Brass snippets are checked too.
        open.push(OpenFence {
            marker,
            count,
            capture,
            start: index + 1,
            code: String::new(),
        });
    }
    examples
}

fn markdown_links(text: &str) -> Vec<(usize, String)> {
    let mut links = Vec::new();
    let mut open: Option<(u8, usize)> = None;
    for (index, line) in text.lines().enumerate() {
        if let Some((marker, count)) = open {
            let close = fence_start(line)
                .is_some_and(|(m, n, rest)| m == marker && n >= count && rest.is_empty());
            if close {
                open = None;
            }
            continue;
        }
        if let Some((marker, count, _)) = fence_start(line) {
            open = Some((marker, count));
            continue;
        }
        let mut rest = line;
        while let Some(start) = rest.find("](") {
            rest = &rest[start + 2..];
            let Some(end) = rest.find(')') else {
                break;
            };
            links.push((index + 1, rest[..end].trim().to_string()));
            rest = &rest[end + 1..];
        }
    }
    links
}

fn heading_slug(heading: &str) -> String {
    heading
        .trim()
        .chars()
        .filter_map(|ch| match ch {
            'A'..='Z' => Some(ch.to_ascii_lowercase()),
            'a'..='z' | '0'..='9' | '-' | '_' => Some(ch),
            ' ' | '\t' => Some('-'),
            _ => None,
        })
        .collect()
}

fn anchors_in(text: &str) -> Vec<String> {
    let mut anchors = Vec::new();
    let mut open: Option<(u8, usize)> = None;
    for line in text.lines() {
        if let Some((marker, count)) = open {
            let close = fence_start(line)
                .is_some_and(|(m, n, rest)| m == marker && n >= count && rest.is_empty());
            if close {
                open = None;
            }
            continue;
        }
        if let Some((marker, count, _)) = fence_start(line) {
            open = Some((marker, count));
            continue;
        }
        let line = line.trim_start();
        let hashes = line.bytes().take_while(|byte| *byte == b'#').count();
        if (1..=6).contains(&hashes) && line.as_bytes().get(hashes) == Some(&b' ') {
            anchors.push(heading_slug(&line[hashes + 1..]));
        }
    }
    anchors
}

fn resolve_doc(root: &Path, source: &Path, route: &str) -> Option<PathBuf> {
    if route.is_empty() {
        return Some(source.to_path_buf());
    }
    let route = route.trim_end_matches('/');
    let base = if let Some(absolute) = route.strip_prefix('/') {
        root.join(absolute)
    } else {
        source.parent().expect("Markdown parent").join(route)
    };
    let candidates = [
        base.clone(),
        base.with_extension("md"),
        base.with_extension("mdx"),
        base.join("index.md"),
        base.join("index.mdx"),
    ];
    candidates.into_iter().find(|path| path.is_file())
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
        let stderr = String::from_utf8_lossy(&output.stderr);
        if !output.status.success() || stderr.contains(": warning:") {
            failures.push(format!(
                "{}:{}\n{}",
                example.source_path.display(),
                example.line,
                stderr
            ));
        }
    }
    let _ = std::fs::remove_dir_all(&scratch);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Internal documentation links must name an existing page and heading. The
/// site build accepts unresolved hrefs, so this catches failures at the source.
#[test]
fn internal_book_links_resolve() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../book/src/content/docs");
    let mut markdown = Vec::new();
    collect_markdown(&root, &mut markdown);
    let mut failures = Vec::new();

    for source in &markdown {
        let text = std::fs::read_to_string(source).expect("read Markdown");
        for (line, target) in markdown_links(&text) {
            if target.starts_with("https://")
                || target.starts_with("http://")
                || target.starts_with("mailto:")
            {
                continue;
            }
            let (route, fragment) = target
                .split_once('#')
                .map_or((target.as_str(), None), |(route, fragment)| {
                    (route, Some(fragment))
                });
            let Some(document) = resolve_doc(&root, source, route) else {
                failures.push(format!(
                    "{}:{line}: missing page `{target}`",
                    source.display()
                ));
                continue;
            };
            if let Some(fragment) = fragment.filter(|fragment| !fragment.is_empty()) {
                let target_text = std::fs::read_to_string(&document).expect("read linked Markdown");
                if !anchors_in(&target_text)
                    .iter()
                    .any(|anchor| anchor == fragment)
                {
                    failures.push(format!(
                        "{}:{line}: missing anchor `#{fragment}` in {}",
                        source.display(),
                        document.display()
                    ));
                }
            }
        }
    }

    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
