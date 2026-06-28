import { WASI, File, OpenFile, ConsoleStdout, PreopenDirectory } from "@bjorn3/browser_wasi_shim";

const wasm = await WebAssembly.compileStreaming(fetch("/playground/prepoly.wasm"));

const execute = async () => {
  const stdout = document.getElementById("stdout")!;
  stdout.innerHTML = "";
  const stderr = document.getElementById("stderr")!;
  stderr.innerHTML = "";

  const program = (document.getElementById("program") as HTMLTextAreaElement).value;

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

(document.getElementById("program") as HTMLTextAreaElement).value = `fun gcd(a, b) {
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
`;
