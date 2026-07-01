import { WASI, File, OpenFile, ConsoleStdout, PreopenDirectory } from "@bjorn3/browser_wasi_shim";
import * as monaco from "monaco-editor";
import {
  PrepolyLsp,
  SEMANTIC_LEGEND,
  type CompletionItem,
  type Diagnostic,
  type Hover,
  type Range,
} from "./lsp";

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
println("GCD is {result}")


// Type definition example
type Person = {
    first_name: string,
    last_name: string,
}
fun Person.display(self) {
    return "{self.first_name} {self.last_name}"
}
fun get_display_name(obj) {
    if let person = Person.from(obj) {
        return person.display()
    } else {
        error("not a Person type")!
    }
}
println(
    get_display_name({
        first_name: "Grace",
        last_name: "Hopper",
    })
)
println(
    get_display_name({
        name: "Haskell Curry",
        age: 125,
    })
)`;

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

  monaco.languages.registerCompletionItemProvider("prepoly", {
    // `.` / `{` continue member access and import paths; identifier typing
    // triggers completion on its own. Mirrors the server's trigger characters.
    triggerCharacters: [".", "{"],
    provideCompletionItems: async (model, position) => {
      const items = await lsp.completion(model.getValue(), toLspPosition(position));
      // Replace the word under the cursor, so an accepted item overwrites the
      // already-typed prefix instead of appending to it.
      const word = model.getWordUntilPosition(position);
      const range: monaco.IRange = {
        startLineNumber: position.lineNumber,
        endLineNumber: position.lineNumber,
        startColumn: word.startColumn,
        endColumn: word.endColumn,
      };
      return { suggestions: items.map((item) => toCompletion(item, range)) };
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

// LSP and Monaco both number their completion-item kinds, but with different
// values, so map by the LSP value (1..=25) to the named Monaco enum.
const lspKindToMonaco: Record<number, monaco.languages.CompletionItemKind> = (() => {
  const k = monaco.languages.CompletionItemKind;
  return {
    1: k.Text, 2: k.Method, 3: k.Function, 4: k.Constructor, 5: k.Field,
    6: k.Variable, 7: k.Class, 8: k.Interface, 9: k.Module, 10: k.Property,
    11: k.Unit, 12: k.Value, 13: k.Enum, 14: k.Keyword, 15: k.Snippet,
    16: k.Color, 17: k.File, 18: k.Reference, 19: k.Folder, 20: k.EnumMember,
    21: k.Constant, 22: k.Struct, 23: k.Event, 24: k.Operator, 25: k.TypeParameter,
  };
})();

const toCompletion = (
  item: CompletionItem,
  range: monaco.IRange,
): monaco.languages.CompletionItem => ({
  label: item.label,
  kind: lspKindToMonaco[item.kind ?? 1] ?? monaco.languages.CompletionItemKind.Text,
  detail: item.detail,
  insertText: item.insertText ?? item.label,
  range,
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
