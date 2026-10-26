-- Brass language server definition for the native `vim.lsp.enable("brass")`
-- workflow (Neovim 0.11+). With this directory on the runtimepath, Neovim loads
-- this file to resolve the `brass` server config; `vim.lsp.enable("brass")`
-- then attaches it to `brass` buffers.
--
-- Override any field from your own config without editing this file, e.g. to
-- point `cmd` at a locally built binary:
--   vim.lsp.config("brass", { cmd = { "/path/to/target/debug/czls" } })

return {
  cmd = { "czpm", "lsp" },
  filetypes = { "brass" },
  -- Imports resolve relative to each file's own directory, so a project root is
  -- optional; with no marker found the server still attaches as a single file.
  root_markers = { ".git" },
}
