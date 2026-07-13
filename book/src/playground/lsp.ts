//! Browser-side bridge to the Prepoly LSP server (`ppls.wasm`).
//!
//! The server is an ordinary stdio LSP process: it reads `Content-Length`
//! framed JSON-RPC from stdin and writes framed replies to stdout. A browser
//! has no threads and no blocking stdin, so instead of keeping one server alive
//! we run a fresh WASI instance per query -- feed it the lifecycle handshake, a
//! `didOpen` carrying the current text, and the feature request, let it run to
//! stdin EOF, then parse everything it wrote. This mirrors how the interpreter
//! wasm is run once per "Execute" and needs no SharedArrayBuffer or cross-origin
//! isolation, so it also works on static hosting.

import {
  WASI,
  File,
  OpenFile,
  ConsoleStdout,
  PreopenDirectory,
  WASIProcExit,
} from "@bjorn3/browser_wasi_shim";

/// The single in-memory document the playground edits. Feature requests address
/// it by this URI, and `did_open` registers it under the same key server-side.
export const DOC_URI = "file:///main.pp";

/// Semantic-token legend, mirroring the server's `TOKEN_TYPES`/`TOKEN_MODIFIERS`
/// order exactly so the delta-encoded `tokenType`/`tokenModifiers` indices the
/// server emits resolve to the right names in Monaco. Keep in sync with
/// `crates/prepoly_language_server/src/features/semantic_tokens.rs`.
export const SEMANTIC_LEGEND = {
  tokenTypes: [
    "namespace",
    "type",
    "enum",
    "function",
    "method",
    "property",
    "variable",
    "parameter",
    "keyword",
    "string",
    "number",
    "operator",
    "enumMember",
    "comment",
  ],
  tokenModifiers: ["declaration", "defaultLibrary"],
};

// Minimal shapes of the LSP payloads the playground consumes. These are the
// wire JSON, with 0-based UTF-16 positions; callers convert to Monaco's 1-based
// positions.
export interface Position {
  line: number;
  character: number;
}
export interface Range {
  start: Position;
  end: Position;
}
export interface Diagnostic {
  range: Range;
  severity?: number; // 1=Error 2=Warning 3=Information 4=Hint
  message: string;
  source?: string;
}
export interface Location {
  uri: string;
  range: Range;
}
export interface Hover {
  contents:
    | string
    | { value: string }
    | Array<string | { language?: string; value: string }>;
  range?: Range;
}
export interface CompletionItem {
  label: string;
  kind?: number; // LSP CompletionItemKind (1..=25)
  detail?: string;
  insertText?: string;
}

const encoder = new TextEncoder();
const decoder = new TextDecoder();

interface JsonRpcMessage {
  jsonrpc?: string;
  id?: number;
  method?: string;
  params?: unknown;
  result?: unknown;
  error?: unknown;
}

/// Frame one JSON-RPC message in LSP's `Content-Length` envelope. The length is
/// the UTF-8 byte count of the body, so headers and body are concatenated as
/// bytes rather than strings.
function frame(message: object): Uint8Array {
  const body = encoder.encode(JSON.stringify(message));
  const header = encoder.encode(`Content-Length: ${body.length}\r\n\r\n`);
  const out = new Uint8Array(header.length + body.length);
  out.set(header, 0);
  out.set(body, header.length);
  return out;
}

function concat(chunks: Uint8Array[]): Uint8Array {
  const total = chunks.reduce((n, c) => n + c.length, 0);
  const out = new Uint8Array(total);
  let offset = 0;
  for (const chunk of chunks) {
    out.set(chunk, offset);
    offset += chunk.length;
  }
  return out;
}

/// Offset of the `\r\n\r\n` header/body separator at or after `from`, or -1.
function headerEnd(bytes: Uint8Array, from: number): number {
  for (let i = from; i + 3 < bytes.length; i++) {
    if (
      bytes[i] === 0x0d &&
      bytes[i + 1] === 0x0a &&
      bytes[i + 2] === 0x0d &&
      bytes[i + 3] === 0x0a
    ) {
      return i;
    }
  }
  return -1;
}

/// Split a captured stdout buffer into its JSON-RPC messages. `Content-Length`
/// counts bytes, so the body is sliced on the byte array (not a decoded string)
/// to stay correct when a payload carries multi-byte UTF-8.
function parseMessages(bytes: Uint8Array): JsonRpcMessage[] {
  const messages: JsonRpcMessage[] = [];
  let pos = 0;
  while (pos < bytes.length) {
    const sep = headerEnd(bytes, pos);
    if (sep < 0) break;
    const header = decoder.decode(bytes.subarray(pos, sep));
    const match = /content-length:\s*(\d+)/i.exec(header);
    if (!match) break;
    const start = sep + 4;
    const end = start + Number(match[1]);
    if (end > bytes.length) break;
    try {
      messages.push(JSON.parse(decoder.decode(bytes.subarray(start, end))));
    } catch {
      break; // a truncated final frame ends parsing
    }
    pos = end;
  }
  return messages;
}

/// A query against the Prepoly LSP server: one fresh server run, returning the
/// reply to the request with id 1 plus any notifications (e.g. published
/// diagnostics) the run emitted.
export class PrepolyLsp {
  private readonly module: WebAssembly.Module;

  constructor(module: WebAssembly.Module) {
    this.module = module;
  }

  /// Run a server instance over the lifecycle handshake, a `did_open` for the
  /// current `text`, and `requests`, returning every message it wrote. The
  /// instance reads to stdin EOF and exits; nothing persists between calls, so
  /// each request must reopen the document -- which `text` here does.
  private async run(
    text: string,
    requests: object[],
  ): Promise<JsonRpcMessage[]> {
    const stdin = concat([
      frame({
        jsonrpc: "2.0",
        id: 0,
        method: "initialize",
        params: { processId: null, rootUri: null, capabilities: {} },
      }),
      frame({ jsonrpc: "2.0", method: "initialized", params: {} }),
      frame({
        jsonrpc: "2.0",
        method: "textDocument/didOpen",
        params: {
          textDocument: {
            uri: DOC_URI,
            languageId: "prepoly",
            version: 1,
            text,
          },
        },
      }),
      ...requests.map(frame),
    ]);

    // stdout is captured into an in-memory file: OpenFile.fd_write appends to
    // its backing File, so the full transport is in `stdout.data` afterwards.
    const stdout = new File([]);
    const fds = [
      new OpenFile(new File(stdin)), // fd 0: framed requests, then EOF
      new OpenFile(stdout), // fd 1: captured LSP replies
      ConsoleStdout.lineBuffered(() => {}), // fd 2: server tracing, discarded
      new PreopenDirectory(".", new Map()), // cwd, for best-effort import paths
    ];
    const wasi = new WASI(["ppls"], [], fds);
    const inst = await WebAssembly.instantiate(this.module, {
      wasi_snapshot_preview1: wasi.wasiImport,
    });
    try {
      // Returns when the server hits stdin EOF and main returns; a clean
      // `proc_exit` is swallowed by `start`. Other traps surface here.
      wasi.start(
        inst as unknown as {
          exports: { _start: () => unknown; memory: WebAssembly.Memory };
        },
      );
    } catch (err) {
      if (!(err instanceof WASIProcExit)) {
        console.error("ppls crashed", err);
      }
    }
    return parseMessages(stdout.data);
  }

  private static reply(
    messages: JsonRpcMessage[],
    id: number,
  ): JsonRpcMessage | undefined {
    return messages.find((m) => m.id === id && m.method === undefined);
  }

  /// Diagnostics for `text`, via the pull `textDocument/diagnostic` request.
  /// The server also pushes diagnostics on `did_open`, but the one-shot
  /// transport tears down before a pushed notification is flushed, so the
  /// request/response form is used instead -- the wasm server advertises and
  /// answers it for exactly this reason.
  async diagnostics(text: string): Promise<Diagnostic[]> {
    const messages = await this.run(text, [
      {
        jsonrpc: "2.0",
        id: 1,
        method: "textDocument/diagnostic",
        params: { textDocument: { uri: DOC_URI } },
      },
    ]);
    const report = PrepolyLsp.reply(messages, 1)?.result as {
      items?: Diagnostic[];
    } | null;
    return report?.items ?? [];
  }

  async hover(text: string, position: Position): Promise<Hover | null> {
    const messages = await this.run(text, [
      {
        jsonrpc: "2.0",
        id: 1,
        method: "textDocument/hover",
        params: { textDocument: { uri: DOC_URI }, position },
      },
    ]);
    return (PrepolyLsp.reply(messages, 1)?.result as Hover | null) ?? null;
  }

  async definition(text: string, position: Position): Promise<Location | null> {
    const messages = await this.run(text, [
      {
        jsonrpc: "2.0",
        id: 1,
        method: "textDocument/definition",
        params: { textDocument: { uri: DOC_URI }, position },
      },
    ]);
    const result = PrepolyLsp.reply(messages, 1)?.result as
      Location | Location[] | null;
    if (!result) return null;
    return Array.isArray(result) ? (result[0] ?? null) : result;
  }

  /// Completion proposals at `position`. The server returns the full candidate
  /// set (member methods, in-scope symbols, import names); the editor filters
  /// them against the typed prefix.
  async completion(
    text: string,
    position: Position,
  ): Promise<CompletionItem[]> {
    const messages = await this.run(text, [
      {
        jsonrpc: "2.0",
        id: 1,
        method: "textDocument/completion",
        params: { textDocument: { uri: DOC_URI }, position },
      },
    ]);
    const result = PrepolyLsp.reply(messages, 1)?.result as
      CompletionItem[] | { items?: CompletionItem[] } | null;
    if (!result) return [];
    return Array.isArray(result) ? result : (result.items ?? []);
  }

  /// The document's semantic tokens as the protocol's flat delta-encoded
  /// integer array, ready to wrap in a `Uint32Array` for Monaco.
  async semanticTokens(text: string): Promise<number[]> {
    const messages = await this.run(text, [
      {
        jsonrpc: "2.0",
        id: 1,
        method: "textDocument/semanticTokens/full",
        params: { textDocument: { uri: DOC_URI } },
      },
    ]);
    return (
      (PrepolyLsp.reply(messages, 1)?.result as { data?: number[] } | null)
        ?.data ?? []
    );
  }
}
