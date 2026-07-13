-- Prepoly language server definition for the native `vim.lsp.enable("prepoly")`
-- workflow (Neovim 0.11+). With this directory on the runtimepath, Neovim loads
-- this file to resolve the `prepoly` server config; `vim.lsp.enable("prepoly")`
-- then attaches it to `prepoly` buffers.
--
-- Override any field from your own config without editing this file, e.g. to
-- point `cmd` at a locally built binary:
--   vim.lsp.config("prepoly", { cmd = { "/path/to/target/debug/ppls" } })

return {
  cmd = { "ppm", "lsp" },
  filetypes = { "prepoly" },
  -- Imports resolve relative to each file's own directory, so a project root is
  -- optional; with no marker found the server still attaches as a single file.
  root_markers = { ".git" },
}
