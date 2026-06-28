# Prepoly language server in Neovim

Diagnostics, hover types, go-to-definition, and semantic-token highlighting for
`.pp` files, backed by `prepoly-lsp` (the `prepoly_language_server` crate).

## 1. Build the server

```sh
# Install onto PATH (recommended):
cargo install --path crates/prepoly_language_server   # -> ~/.cargo/bin/prepoly-lsp

# ...or just build it and point `cmd` at the binary:
cargo build -p prepoly_language_server                # -> target/debug/prepoly-lsp
```

`prepoly-lsp` has no LLVM dependency, so it builds without the JIT toolchain.

## 2. Make this directory available to Neovim

This folder is a minimal plugin (`lua/prepoly.lua`). Add it to your runtimepath
with a plugin manager, or copy `lua/prepoly.lua` into your config's `lua/`.

### lazy.nvim

```lua
{
  dir = "/path/to/prepoly/editors/nvim",
  dependencies = { "neovim/nvim-lspconfig" },
  -- Register the filetype at startup so the first `.pp` buffer is recognised,
  -- then lazy-load the LSP setup when a prepoly file opens.
  init = function()
    vim.filetype.add({ extension = { pp = "prepoly" } })
  end,
  ft = "prepoly",
  config = function()
    require("prepoly").setup({})
  end,
}
```

### packer / vim-plug + manual setup

```lua
-- after the plugin (this directory) is on the runtimepath:
require("prepoly").setup({})
```

If you built the binary instead of installing it, pass its path:

```lua
require("prepoly").setup({
  cmd = { vim.fn.getcwd() .. "/target/debug/prepoly-lsp" },
})
```

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

## Notes

- `.pp` is also Puppet's extension. `vim.filetype.add` (used by `setup` and the
  lazy.nvim `init` above) overrides that mapping for prepoly.
- Imports are resolved from each file's directory on disk, so unsaved edits in
  *other* open files are not yet reflected across files; the active file is
  always analyzed from its live buffer contents.
- Set `PREPOLY_LOG=debug` in the environment to get server-side trace logs on
  stderr (visible via `:LspLog`).
