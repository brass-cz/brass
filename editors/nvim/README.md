# Prepoly language server in Neovim

Diagnostics, hover types, go-to-definition, and semantic-token highlighting for
`.pp` files, backed by `ppls` (the `prepoly_language_server` crate).

Uses the native Neovim 0.11+ LSP workflow: a server definition in `lsp/`, the
filetype mapping in `ftdetect/`, and `vim.lsp.enable("prepoly")` to start it.

## 1. Build the server

```sh
# Install onto PATH (recommended):
cargo install --path crates/prepoly_language_server   # -> ~/.cargo/bin/ppls

# ...or just build it and override `cmd` to point at the binary (see below):
cargo build -p prepoly_language_server                # -> target/debug/ppls
```

`ppls` has no LLVM dependency, so it builds without the JIT toolchain.

## 2. Put this directory on the runtimepath and enable the server

This folder is a minimal plugin: `lsp/prepoly.lua` (server config) and
`ftdetect/prepoly.lua` (the `.pp` -> `prepoly` filetype mapping).

### lazy.nvim

```lua
{
  dir = "/path/to/prepoly/editors/nvim",
  ft = "prepoly", -- lazy.nvim sources ftdetect/ at startup, so this triggers correctly
  config = function()
    vim.lsp.enable("prepoly")
  end,
}
```

### Manual (any setup with this directory on the runtimepath)

```lua
vim.opt.runtimepath:append("/path/to/prepoly/editors/nvim")
vim.lsp.enable("prepoly")
```

### Using a locally built binary instead of one on PATH

Override `cmd` before enabling; the override merges over `lsp/prepoly.lua`:

```lua
vim.lsp.config("prepoly", {
  cmd = { vim.fn.getcwd() .. "/target/debug/ppls" },
})
vim.lsp.enable("prepoly")
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

- `.pp` is also Puppet's extension; `ftdetect/prepoly.lua` overrides that.
- Imports are resolved from each file's directory on disk, so unsaved edits in
  *other* open files are not yet reflected across files; the active file is
  always analyzed from its live buffer contents.
- Set `PREPOLY_LOG=debug` in the environment for server-side trace logs on
  stderr (visible via `:LspLog`).
