/// Run a prepoly program through the wasm interpreter. Shared by the
/// playground editor and the runnable code blocks in the docs: the program
/// text becomes `main.pp` in a fresh WASI file system, and stdout/stderr lines
/// stream to the given callbacks.

import {
  WASI,
  File,
  OpenFile,
  ConsoleStdout,
  PreopenDirectory,
  WASIProcExit,
} from "@bjorn3/browser_wasi_shim";

// The interpreter wasm is copied into `public/` by the `prebuild` script, so
// it is served from the site root. Compiled once per page, on first use.
let interpPromise: Promise<WebAssembly.Module> | undefined;

export const loadInterpreter = () =>
  (interpPromise ??= WebAssembly.compileStreaming(fetch("/prepoly.wasm")));

export const runProgram = async (
  program: string,
  onStdout: (line: string) => void,
  onStderr: (line: string) => void,
): Promise<void> => {
  const module = await loadInterpreter();

  const args = ["prepoly", "main.pp"];
  const fds = [
    new OpenFile(new File([])),
    ConsoleStdout.lineBuffered(onStdout),
    ConsoleStdout.lineBuffered(onStderr),
    new PreopenDirectory(
      ".",
      new Map([["main.pp", new File(new TextEncoder().encode(program))]]),
    ),
  ];
  const wasi = new WASI(args, [], fds);

  const inst = await WebAssembly.instantiate(module, {
    wasi_snapshot_preview1: wasi.wasiImport,
  });

  try {
    wasi.start(inst as any);
  } catch (err) {
    // A non-zero exit (e.g. a type error) surfaces as WASIProcExit; its
    // diagnostics already went to stderr, so the exit itself is not an error.
    if (!(err instanceof WASIProcExit)) {
      throw err;
    }
  }
};
