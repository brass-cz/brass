//! End-to-end test of the `ppls` binary over the LSP stdio transport.
//!
//! Unlike the in-process tests in `src/tests.rs` (which call the feature
//! functions directly), this spawns the built server and exchanges real
//! `Content-Length`-framed JSON-RPC, exercising the whole path: capability
//! advertisement, document sync, pushed diagnostics, hover, go-to-definition,
//! completion, and formatting.
//!
//! The LSP lifecycle is honoured -- `initialize` is awaited before any request,
//! and each request's response is read before the next is sent -- because
//! batching everything (and `exit`) at once cancels the in-flight handshake.

use std::io::{BufRead, BufReader, Write};
use std::process::{ChildStdin, Command, Stdio};
use std::sync::mpsc;
use std::time::Duration;

use serde_json::{Value, json};

/// A self-contained program: a type and a function to resolve, a call to hover
/// and jump to, and a type error to surface as a diagnostic.
const SRC: &str = concat!(
    "type Point = {\n",
    "    x: int32\n",
    "}\n",
    "\n",
    "fun helper() -> int32 {\n",
    "    return 1\n",
    "}\n",
    "\n",
    "fun main() {\n",
    "    let p = Point { x: 1 }\n",
    "    let v = helper()\n",
    "    let bad: int32 = \"oops\"\n",
    "}\n",
);

const URI: &str = "file:///tmp/prepoly_e2e/main.pp";

/// A second, badly laid-out document for the formatting request.
const FMT_SRC: &str = "fun f( )   {\n  let x=1+2\n}\n";
const FMT_URI: &str = "file:///tmp/prepoly_e2e/fmt.pp";

#[test]
fn server_answers_hover_definition_completion_and_diagnostics() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_ppls"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn ppls");

    let mut stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();

    // Run the whole conversation on a thread so a hung server fails the test by
    // timeout instead of blocking it forever.
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let mut reader = BufReader::new(stdout);
        let mut seen: Vec<Value> = Vec::new();

        // `helper` in `    let v = helper()` (line 10) starts at column 12.
        let pos = json!({ "line": 10, "character": 13 });
        let at = |id: i64, method: &str| {
            json!({"jsonrpc":"2.0","id":id,"method":method,
                "params":{"textDocument":{"uri":URI},"position":pos}})
        };

        send(
            &mut stdin,
            &json!({"jsonrpc":"2.0","id":1,"method":"initialize",
            "params":{"capabilities":{},"rootUri":null}}),
        );
        read_until(&mut reader, &mut seen, 1);

        send(
            &mut stdin,
            &json!({"jsonrpc":"2.0","method":"initialized","params":{}}),
        );
        send(
            &mut stdin,
            &json!({"jsonrpc":"2.0","method":"textDocument/didOpen",
            "params":{"textDocument":{"uri":URI,"languageId":"prepoly","version":1,"text":SRC}}}),
        );

        send(&mut stdin, &at(2, "textDocument/hover"));
        read_until(&mut reader, &mut seen, 2);
        send(&mut stdin, &at(3, "textDocument/definition"));
        read_until(&mut reader, &mut seen, 3);
        send(
            &mut stdin,
            &json!({"jsonrpc":"2.0","id":4,"method":"textDocument/completion",
            "params":{"textDocument":{"uri":URI},"position":pos,"context":{"triggerKind":1}}}),
        );
        read_until(&mut reader, &mut seen, 4);

        send(
            &mut stdin,
            &json!({"jsonrpc":"2.0","method":"textDocument/didOpen",
            "params":{"textDocument":{"uri":FMT_URI,"languageId":"prepoly","version":1,"text":FMT_SRC}}}),
        );
        send(
            &mut stdin,
            &json!({"jsonrpc":"2.0","id":5,"method":"textDocument/formatting",
            "params":{"textDocument":{"uri":FMT_URI},"options":{"tabSize":4,"insertSpaces":true}}}),
        );
        read_until(&mut reader, &mut seen, 5);

        send(
            &mut stdin,
            &json!({"jsonrpc":"2.0","id":6,"method":"shutdown","params":{}}),
        );
        read_until(&mut reader, &mut seen, 6);
        send(
            &mut stdin,
            &json!({"jsonrpc":"2.0","method":"exit","params":{}}),
        );

        let _ = tx.send(seen);
    });

    let seen = match rx.recv_timeout(Duration::from_secs(30)) {
        Ok(seen) => seen,
        Err(_) => {
            let _ = child.kill();
            panic!("ppls did not complete the conversation within 30s");
        }
    };
    let _ = child.wait();

    // initialize: the features this server provides are advertised.
    let caps = &response(&seen, 1)["capabilities"];
    assert!(!caps["hoverProvider"].is_null(), "hover capability: {caps}");
    assert!(
        !caps["definitionProvider"].is_null(),
        "definition capability: {caps}"
    );
    assert!(
        !caps["completionProvider"].is_null(),
        "completion capability: {caps}"
    );

    // didOpen pushes diagnostics; the `bad` type error must be among them.
    let diags = published_diagnostics(&seen).expect("publishDiagnostics for the document");
    assert!(
        !diags.is_empty(),
        "the type error should be reported: {diags:?}"
    );

    // hover over the call shows `helper`'s signature.
    let hover = response(&seen, 2);
    let hover_text = hover["contents"]["value"].as_str().unwrap_or("");
    assert!(hover_text.contains("fun helper"), "hover: {hover}");

    // go-to-definition jumps to `helper`'s declaration on line 4.
    let def = response(&seen, 3);
    assert_eq!(def["range"]["start"]["line"], json!(4), "definition: {def}");

    // completion offers the in-scope types and functions.
    let labels: Vec<String> = response(&seen, 4)
        .as_array()
        .expect("completion is an item array")
        .iter()
        .filter_map(|i| i["label"].as_str().map(str::to_string))
        .collect();
    for want in ["helper", "Point", "println"] {
        assert!(
            labels.contains(&want.to_string()),
            "completion {want}: {labels:?}"
        );
    }

    // formatting replaces the badly laid-out document in one whole-file edit.
    let edits = response(&seen, 5);
    let edits = edits.as_array().expect("formatting returns an edit array");
    assert_eq!(edits.len(), 1, "one whole-document edit: {edits:?}");
    assert_eq!(
        edits[0]["newText"],
        json!("fun f() {\n    let x = 1 + 2\n}\n"),
        "formatted text: {edits:?}"
    );
    assert_eq!(
        edits[0]["range"]["start"],
        json!({"line": 0, "character": 0})
    );
}

/// Write one `Content-Length`-framed JSON-RPC message.
fn send(stdin: &mut ChildStdin, value: &Value) {
    let body = serde_json::to_vec(value).unwrap();
    write!(stdin, "Content-Length: {}\r\n\r\n", body.len()).unwrap();
    stdin.write_all(&body).unwrap();
    stdin.flush().unwrap();
}

/// A document whose SYNC behaviour is under test: clean, then edited to carry a
/// type error, then edited to carry a syntax error.
const SYNC_URI: &str = "file:///tmp/prepoly_e2e/sync.pp";
const SYNC_CLEAN: &str = "fun main() {\n    let n: int32 = 1\n    println(n)\n}\n";
const SYNC_TYPE_ERROR: &str = "fun main() {\n    let n: int32 = \"oops\"\n    println(n)\n}\n";
const SYNC_SYNTAX_ERROR: &str = "fun main() {\n    let n: int32 = )\n    println(n)\n}\n";

/// Type inference runs on SAVE, not on every keystroke: an edit that introduces a
/// type error publishes nothing until the file is saved, while a syntax error is
/// reported straight away (parsing is cheap, and a half-typed line is a syntax
/// error long before it is a type error).
#[test]
fn type_diagnostics_arrive_on_save_and_syntax_diagnostics_on_change() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_ppls"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn ppls");

    let mut stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();

    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let mut reader = BufReader::new(stdout);
        let mut seen: Vec<Value> = Vec::new();

        send(
            &mut stdin,
            &json!({"jsonrpc":"2.0","id":1,"method":"initialize",
            "params":{"capabilities":{},"rootUri":null}}),
        );
        read_until(&mut reader, &mut seen, 1);
        send(
            &mut stdin,
            &json!({"jsonrpc":"2.0","method":"initialized","params":{}}),
        );

        // Each step's diagnostics are drained before the next, so the published
        // sets stay in step with the notification that produced them.
        send(
            &mut stdin,
            &json!({"jsonrpc":"2.0","method":"textDocument/didOpen",
            "params":{"textDocument":{"uri":SYNC_URI,"languageId":"prepoly","version":1,"text":SYNC_CLEAN}}}),
        );
        let opened = next_diagnostics(&mut reader, &mut seen);

        let change = |text: &str, version: i64| {
            json!({"jsonrpc":"2.0","method":"textDocument/didChange",
            "params":{"textDocument":{"uri":SYNC_URI,"version":version},
                      "contentChanges":[{"text":text}]}})
        };
        send(&mut stdin, &change(SYNC_TYPE_ERROR, 2));
        let typed = next_diagnostics(&mut reader, &mut seen);

        send(
            &mut stdin,
            &json!({"jsonrpc":"2.0","method":"textDocument/didSave",
            "params":{"textDocument":{"uri":SYNC_URI}}}),
        );
        let saved = next_diagnostics(&mut reader, &mut seen);

        send(&mut stdin, &change(SYNC_SYNTAX_ERROR, 3));
        let broken = next_diagnostics(&mut reader, &mut seen);

        send(
            &mut stdin,
            &json!({"jsonrpc":"2.0","id":9,"method":"shutdown","params":{}}),
        );
        read_until(&mut reader, &mut seen, 9);
        send(
            &mut stdin,
            &json!({"jsonrpc":"2.0","method":"exit","params":{}}),
        );
        let _ = tx.send((opened, typed, saved, broken, seen));
    });

    let (opened, typed, saved, broken, seen) = match rx.recv_timeout(Duration::from_secs(30)) {
        Ok(v) => v,
        Err(_) => {
            let _ = child.kill();
            panic!("ppls did not complete the conversation within 30s");
        }
    };
    let _ = child.wait();

    // `save` must be advertised, or the client never sends the notification the
    // type check now hangs off.
    let sync = &response(&seen, 1)["capabilities"]["textDocumentSync"];
    assert_eq!(sync["save"], json!(true), "save must be advertised: {sync}");

    assert!(opened.is_empty(), "the clean document is clean: {opened:?}");
    assert!(
        typed.is_empty(),
        "an edit must not run the type check: {typed:?}"
    );
    assert!(
        messages(&saved).iter().any(|m| m.contains("int32")),
        "saving must publish the type error: {saved:?}"
    );
    assert!(
        messages(&broken)
            .iter()
            .any(|m| m.starts_with("syntax error")),
        "a syntax error is reported on the edit itself: {broken:?}"
    );
}

/// The messages of a diagnostic set.
fn messages(diags: &[Value]) -> Vec<String> {
    diags
        .iter()
        .map(|d| d["message"].as_str().unwrap_or("").to_string())
        .collect()
}

/// Read framed messages until the next `publishDiagnostics` and return its
/// diagnostics, collecting everything read into `seen`.
fn next_diagnostics(reader: &mut impl BufRead, seen: &mut Vec<Value>) -> Vec<Value> {
    while let Some(msg) = read_message(reader) {
        let published = (msg["method"] == json!("textDocument/publishDiagnostics"))
            .then(|| msg["params"]["diagnostics"].as_array().cloned())
            .flatten();
        seen.push(msg);
        if let Some(diags) = published {
            return diags;
        }
    }
    panic!("stream ended before the next publishDiagnostics");
}

/// Read framed messages into `seen` until one with response id `id` arrives,
/// so notifications (e.g. pushed diagnostics) are collected along the way.
fn read_until(reader: &mut impl BufRead, seen: &mut Vec<Value>, id: i64) {
    while let Some(msg) = read_message(reader) {
        let is_target = msg["id"] == json!(id);
        seen.push(msg);
        if is_target {
            return;
        }
    }
}

/// Read a single `Content-Length`-framed message, or `None` at end of stream.
fn read_message(reader: &mut impl BufRead) -> Option<Value> {
    let mut len = 0usize;
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line).ok()? == 0 {
            return None;
        }
        let line = line.trim_end();
        if line.is_empty() {
            break;
        }
        if let Some(n) = line.strip_prefix("Content-Length:") {
            len = n.trim().parse().ok()?;
        }
    }
    let mut body = vec![0u8; len];
    reader.read_exact(&mut body).ok()?;
    serde_json::from_slice(&body).ok()
}

/// The `result` of the response with the given request id.
fn response(messages: &[Value], id: i64) -> Value {
    messages
        .iter()
        .find(|m| m["id"] == json!(id) && m.get("result").is_some())
        .unwrap_or_else(|| panic!("no response for id {id} in {messages:?}"))["result"]
        .clone()
}

/// The diagnostics of the first `publishDiagnostics` notification.
fn published_diagnostics(messages: &[Value]) -> Option<Vec<Value>> {
    messages
        .iter()
        .find(|m| m["method"] == json!("textDocument/publishDiagnostics"))
        .and_then(|m| m["params"]["diagnostics"].as_array().cloned())
}
