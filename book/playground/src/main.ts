import { WASI, File, OpenFile, ConsoleStdout, PreopenDirectory } from "@bjorn3/browser_wasi_shim";
import * as monaco from "monaco-editor";
import { PrepolyLsp, SEMANTIC_LEGEND, type Diagnostic, type Hover, type Range } from "./lsp";

const wasm = await WebAssembly.compileStreaming(fetch("/playground/prepoly.wasm"));

// The language server is optional: if its wasm has not been built/published the
// editor still runs, just without diagnostics, hover, go-to-definition, and
// semantic highlighting.
const lspModule = await WebAssembly.compileStreaming(fetch("/playground/prepoly-lsp.wasm")).catch(
  (err) => {
    console.warn("prepoly-lsp.wasm unavailable; language features disabled", err);
    return null;
  },
);

const sampleProgram = `fun gcd(a, b) {
    if b == 0 {
        return a
    } else {
        return gcd(b, a % b)
    }
}

const elems = [16, 36, 72, 192]
let result = elems[0]
for elem in elems.slice(1, elems.len()) {
    result = gcd(result, elem)
}

println("GCD is {result}")`;

const setupMonaco = async () => {
  monaco.languages.register({ id: "prepoly" });

  const editor = monaco.editor.create(document.getElementById("program-container")!, {
    language: "prepoly",
    theme: "vs-dark",
    value: sampleProgram,
    // Pull semantic tokens from the registered provider below.
    "semanticHighlighting.enabled": true,
    fontSize: 18,
  });

  if (lspModule) {
    wireLanguageFeatures(editor, new PrepolyLsp(lspModule));
  }

  return editor;
}

/// Drive Monaco's diagnostics, hover, go-to-definition, and semantic-token
/// surfaces from the wasm LSP server. Each provider hands the current document
/// text to `lsp`, which runs a one-shot server query (see `./lsp`), and the LSP
/// results are converted into Monaco's 1-based coordinate space.
const wireLanguageFeatures = (
  editor: monaco.editor.IStandaloneCodeEditor,
  lsp: PrepolyLsp,
) => {
  const model = editor.getModel()!;

  // Diagnostics are pushed by the server, not pulled, so we recompute them on
  // edit (debounced) and on load, publishing them as model markers.
  const refreshDiagnostics = debounce(async () => {
    const diagnostics = await lsp.diagnostics(model.getValue());
    monaco.editor.setModelMarkers(model, "prepoly", diagnostics.map(toMarker));
  }, 300);
  model.onDidChangeContent(refreshDiagnostics);
  refreshDiagnostics();

  monaco.languages.registerHoverProvider("prepoly", {
    provideHover: async (model, position) => {
      const hover = await lsp.hover(model.getValue(), toLspPosition(position));
      if (!hover) return null;
      return { contents: [{ value: hoverText(hover.contents) }], range: hover.range && toRange(hover.range) };
    },
  });

  monaco.languages.registerDefinitionProvider("prepoly", {
    provideDefinition: async (model, position) => {
      const location = await lsp.definition(model.getValue(), toLspPosition(position));
      if (!location) return null;
      // Single-file playground: every location resolves into this one model.
      return { uri: model.uri, range: toRange(location.range) };
    },
  });

  monaco.languages.registerDocumentSemanticTokensProvider("prepoly", {
    getLegend: () => SEMANTIC_LEGEND,
    provideDocumentSemanticTokens: async (model) => {
      const data = await lsp.semanticTokens(model.getValue());
      return { data: new Uint32Array(data) };
    },
    releaseDocumentSemanticTokens: () => {},
  });
}

// LSP positions are 0-based over UTF-16 code units; Monaco positions are
// 1-based, with column already a UTF-16 offset -- so the two differ only by the
// off-by-one origin.
const toLspPosition = (position: monaco.IPosition) => ({
  line: position.lineNumber - 1,
  character: position.column - 1,
});

const toRange = (range: Range): monaco.IRange => ({
  startLineNumber: range.start.line + 1,
  startColumn: range.start.character + 1,
  endLineNumber: range.end.line + 1,
  endColumn: range.end.character + 1,
});

const severityToMonaco: Record<number, monaco.MarkerSeverity> = {
  1: monaco.MarkerSeverity.Error,
  2: monaco.MarkerSeverity.Warning,
  3: monaco.MarkerSeverity.Info,
  4: monaco.MarkerSeverity.Hint,
};

const toMarker = (diagnostic: Diagnostic): monaco.editor.IMarkerData => ({
  severity: severityToMonaco[diagnostic.severity ?? 1] ?? monaco.MarkerSeverity.Error,
  message: diagnostic.message,
  source: diagnostic.source,
  startLineNumber: diagnostic.range.start.line + 1,
  startColumn: diagnostic.range.start.character + 1,
  endLineNumber: diagnostic.range.end.line + 1,
  endColumn: diagnostic.range.end.character + 1,
});

/// Flatten LSP hover contents (a string, a marked-code object, or an array of
/// either) into one markdown string for Monaco's hover widget.
const hoverText = (contents: Hover["contents"]): string => {
  const one = (part: string | { language?: string; value: string }): string =>
    typeof part === "string" ? part : part.value;
  if (typeof contents === "string") return contents;
  if (Array.isArray(contents)) return contents.map(one).join("\n");
  return contents.value;
};

/// Coalesce rapid edits so each keystroke does not spawn a server run.
const debounce = <A extends unknown[]>(fn: (...args: A) => void, ms: number) => {
  let timer: ReturnType<typeof setTimeout> | undefined;
  return (...args: A) => {
    clearTimeout(timer);
    timer = setTimeout(() => fn(...args), ms);
  };
}

const editor = await setupMonaco();

const execute = async () => {
  const stdout = document.getElementById("stdout")!;
  stdout.innerHTML = "";
  const stderr = document.getElementById("stderr")!;
  stderr.innerHTML = "";

  const program = editor.getValue();

  const args = ["prepoly", "main.pp"];
  const fds = [
    new OpenFile(new File([])),
    ConsoleStdout.lineBuffered((line) => { stdout.innerHTML += `<pre><code>${line}</code></pre>`; }),
    ConsoleStdout.lineBuffered((line) => { stderr.innerHTML += `<pre><code>${line}</code></pre>`; }),
    new PreopenDirectory(".", new Map([
      ["main.pp", new File(new TextEncoder().encode(program))],
    ])),
  ];
  const wasi = new WASI(args, [], fds);

  const inst = await WebAssembly.instantiate(wasm, {
    "wasi_snapshot_preview1": wasi.wasiImport,
  });

  wasi.start(inst as any);
};

document.getElementById("execButton")?.addEventListener("click", execute);
