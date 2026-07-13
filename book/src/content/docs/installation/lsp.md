---
title: "Installing the prepoly LSP server"
description: "Build and install the prepoly LSP server."
---

prepoly provides an LSP server implementation.

Run the following command to install `ppls`:

```bash
./x cargo install --path crates/prepoly_language_server
```

For projects managed with [ppm](/guides/packages/), configure your editor to
launch `ppm lsp` rather than `ppls` directly: it resolves the
dependencies declared in `package.toml` before starting the server, and in a
directory without a `package.toml` it starts the plain server, so the same
configuration works everywhere.

## When diagnostics update

Type diagnostics are published when the file is **saved**, and when it is first
opened. While you type, the server only re-parses, so syntax errors still appear
immediately -- a half-typed line is a syntax error long before it is a type
error.

Type inference re-checks the whole module graph, which is too much work to redo
on every keystroke. Editing clears the previous check's type diagnostics rather
than leaving them behind: their positions no longer describe the text on screen.

Hover, completion and go-to-definition are unaffected -- each request analyzes
the current text, saved or not.
