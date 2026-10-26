# Brass language server in Neovim

Diagnostics, hover types, go-to-definition, completion, formatting, and
semantic-token highlighting for `.cz` files, backed by `czls` (the
`brass_language_server` crate).

Uses the native Neovim 0.11+ LSP workflow: a server definition in `lsp/`, the
filetype mapping in `ftdetect/`, and `vim.lsp.enable("brass")` to start it.

## 1. Build the server

```sh
# Install onto PATH (recommended):
cargo install --path crates/brass_language_server   # -> ~/.cargo/bin/czls

# ...or just build it and override `cmd` to point at the binary (see below):
cargo build -p brass_language_server                # -> target/debug/czls
```

`czls` has no LLVM dependency, so it builds without the JIT toolchain.

The server config launches `czpm lsp`, which resolves a project's
`package.toml` dependencies and then starts `czls` from `PATH` (outside a
project it starts the plain server). The complete toolchain (see
[Installing Brass](../../book/src/content/docs/installation/interpreter.md))
puts both on `PATH`; with only `czls` installed,
[override `cmd`](#overriding-the-server-command).

## 2. Put this directory on the runtimepath and enable the server

This folder is a minimal plugin: `lsp/brass.lua` (server config) and
`ftdetect/brass.lua` (the `.cz` -> `brass` filetype mapping).

### lazy.nvim

```lua
{
  dir = "/path/to/brass/editors/nvim",
  ft = "brass", -- lazy.nvim sources ftdetect/ at startup, so this triggers correctly
  config = function()
    vim.lsp.enable("brass")
  end,
}
```

### Manual (any setup with this directory on the runtimepath)

```lua
vim.opt.runtimepath:append("/path/to/brass/editors/nvim")
vim.lsp.enable("brass")
```

### Overriding the server command

Override `cmd` before enabling; the override merges over `lsp/brass.lua`.
Use `{ "czls" }` to run the server from `PATH` without `czpm`, or point at a
locally built binary:

```lua
vim.lsp.config("brass", {
  cmd = { vim.fn.getcwd() .. "/target/debug/czls" },
})
vim.lsp.enable("brass")
```

Requires Neovim 0.11+. (`lsp/` + `vim.lsp.enable` is the native API; older
Neovim needs nvim-lspconfig's classic `setup` framework instead.)

## 3. Keymaps

Hover (`K`) and go-to-definition (`gd`) are Neovim defaults on 0.11+. To set
them (or other LSP maps) explicitly, use an `LspAttach` autocommand:

```lua
vim.api.nvim_create_autocmd("LspAttach", {
  callback = function(args)
    local buf = args.buf
    local map = function(lhs, rhs) vim.keymap.set("n", lhs, rhs, { buffer = buf }) end
    map("K", vim.lsp.buf.hover)
    map("gd", vim.lsp.buf.definition)
    map("[d", vim.diagnostic.goto_prev)
    map("]d", vim.diagnostic.goto_next)
  end,
})
```

Hover shows a variable's inferred type, a function's signature (unannotated
parameters/returns render as `unknown_0`, `unknown_1`, ...), or a type's
definition.

## 4. Semantic-token highlighting

The built-in LSP client enables semantic tokens automatically when the server
advertises them (it does), so highlighting works on attach with no extra setup.
Token groups (`@lsp.type.function`, `@lsp.type.type`, `@lsp.type.enum`,
`@lsp.type.method`, ...) inherit your colorscheme; override them with
`:highlight` if you want distinct colors.

## 5. Completion

The server offers completion for types and functions in code, module paths in
`import a.b.`, and the exported names in `import a.b.{ ... }`. Trigger it
manually with `<C-x><C-o>` (the omnifunc is set on attach), or auto-complete as
you type by enabling the built-in client completion in your `LspAttach` (Neovim
0.11+):

```lua
vim.api.nvim_create_autocmd("LspAttach", {
  callback = function(args)
    local client = vim.lsp.get_client_by_id(args.data.client_id)
    if client and client:supports_method("textDocument/completion") then
      vim.lsp.completion.enable(true, client.id, args.buf, { autotrigger = true })
    end
  end,
})
```

## Notes

- `ftdetect/brass.lua` maps the `.cz` extension to the `brass` filetype.
- Imports are resolved from each file's directory on disk, so unsaved edits in
  *other* open files are not seen across files; the active file is always
  analyzed from its live buffer contents.
- Set `BRASS_LOG=debug` in the environment for server-side trace logs on
  stderr (visible via `:LspLog`).
