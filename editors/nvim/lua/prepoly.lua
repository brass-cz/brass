-- Neovim integration for the Prepoly language server (`prepoly-lsp`).
--
-- `require('prepoly').setup{}` registers the `prepoly` filetype for `.pp` files
-- and starts the language server. It works both with the classic
-- nvim-lspconfig framework and, on Neovim 0.11+, with the native
-- `vim.lsp.config`/`vim.lsp.enable` API that current nvim-lspconfig builds on --
-- whichever the user has, the same `setup` call configures the server.

local M = {}

-- Map `.pp` to the `prepoly` filetype. `vim.filetype.add` takes precedence over
-- the runtime ftdetect that otherwise maps `*.pp` to Puppet. Call this at
-- startup (e.g. from a plugin manager's `init`) so the first `.pp` buffer is
-- already recognised as prepoly.
function M.register_filetype()
  vim.filetype.add({ extension = { pp = "prepoly" } })
end

-- Configure and start the server.
--
-- `opts` (all optional):
--   cmd          command to launch the server (default `{ "prepoly-lsp" }`)
--   on_attach    callback run when the client attaches to a buffer
--   capabilities client capabilities (e.g. from nvim-cmp/blink.cmp)
--   settings     server settings table
--   root_markers files/dirs that mark a project root (default `{ ".git" }`)
function M.setup(opts)
  opts = opts or {}
  M.register_filetype()

  local config = {
    cmd = opts.cmd or { "prepoly-lsp" },
    filetypes = { "prepoly" },
    on_attach = opts.on_attach,
    capabilities = opts.capabilities,
    settings = opts.settings or {},
  }

  -- Native LSP config (Neovim 0.11+). Imports resolve relative to each file's
  -- directory, so a project root is optional; without a marker the client still
  -- attaches as a single-file server.
  if vim.lsp.config ~= nil and vim.lsp.enable ~= nil then
    config.root_markers = opts.root_markers or { ".git" }
    vim.lsp.config("prepoly", config)
    vim.lsp.enable("prepoly")
    return
  end

  M._setup_classic(config, opts)
end

-- Classic nvim-lspconfig path: register `prepoly` as a custom server the first
-- time, then start it. Used on nvim-lspconfig versions that still expose the
-- `lspconfig.configs` framework.
function M._setup_classic(config, opts)
  local ok, lspconfig = pcall(require, "lspconfig")
  if not ok then
    vim.notify(
      "[prepoly] nvim-lspconfig not found and this Neovim lacks vim.lsp.config",
      vim.log.levels.ERROR
    )
    return
  end
  local configs = require("lspconfig.configs")
  local util = require("lspconfig.util")

  if not configs.prepoly then
    configs.prepoly = {
      default_config = {
        cmd = config.cmd,
        filetypes = config.filetypes,
        root_dir = opts.root_dir or util.root_pattern(".git"),
        single_file_support = true,
      },
      docs = { description = "Prepoly language server (prepoly-lsp)." },
    }
  end

  lspconfig.prepoly.setup({
    on_attach = config.on_attach,
    capabilities = config.capabilities,
    settings = config.settings,
  })
end

return M
