// @ts-check
import fs from "node:fs";
import { defineConfig } from "astro/config";
import starlight from "@astrojs/starlight";

import tailwindcss from "@tailwindcss/vite";

// Shiki has no built-in prepoly support; register the local TextMate grammar
// so ```prepoly fences highlight.
const prepolyGrammar = JSON.parse(
  fs.readFileSync(new URL("./src/grammars/prepoly.tmLanguage.json", import.meta.url), "utf8"),
);

// https://astro.build/config
export default defineConfig({
  integrations: [
    starlight({
      title: "prepoly book",
      head: [
        {
          tag: "meta",
          attrs: { name: "twitter:card", content: "summary" },
        },
      ],
      social: [
        {
          icon: "github",
          label: "GitHub",
          href: "https://github.com/cordx56/prepoly",
        },
      ],
      customCss: ["./src/styles/global.css"],
      components: {
        // Adds the Run button to prepoly code blocks on every docs page.
        Footer: "./src/components/Footer.astro",
      },
      expressiveCode: {
        shiki: {
          langs: [prepolyGrammar],
        },
        plugins: [
          {
            // ```prepoly norun — a valid-prepoly block that must not get a Run
            // button (multi-file, native-only, or intentionally incomplete).
            // The flag is exposed to the client as a data attribute.
            name: "norun",
            hooks: {
              postprocessRenderedBlock: ({ codeBlock, renderData }) => {
                if (codeBlock.metaOptions.getBoolean("norun")) {
                  renderData.blockAst.properties.dataNorun = "";
                }
              },
            },
          },
        ],
      },
      sidebar: [
        {
          label: "Installation",
          items: [
            { label: "The interpreter", slug: "installation/interpreter" },
            { label: "The LSP server", slug: "installation/lsp" },
          ],
        },
        {
          label: "User guide",
          items: [
            { label: "Hello, world!", slug: "guides/hello" },
            { label: "Control flow", slug: "guides/control-flow" },
            { label: "Functions and closures", slug: "guides/functions" },
            { label: "Types and methods", slug: "guides/types" },
            { label: "Pattern matching", slug: "guides/pattern-matching" },
            { label: "Nullable and Result", slug: "guides/null-and-result" },
            { label: "Collections and strings", slug: "guides/collections" },
            { label: "Input and output", slug: "guides/io" },
            { label: "Modules", slug: "guides/modules" },
            { label: "Reflection", slug: "guides/reflection" },
            { label: "Concurrency", slug: "guides/concurrency" },
            { label: "LLM agents", slug: "guides/llm" },
          ],
        },
        {
          label: "References",
          items: [
            { label: "Syntax", slug: "references/syntax" },
            { label: "Type system", slug: "references/types" },
            { label: "Standard library", slug: "references/stdlib" },
            { label: "Modules", slug: "references/modules" },
            { label: "Compile-time reflection", slug: "references/reflection" },
            { label: "Concurrency", slug: "references/concurrency" },
            { label: "Execution model", slug: "references/execution" },
          ],
        },
        { label: "Playground", link: "/playground/" },
      ],
    }),
  ],

  vite: {
    plugins: [tailwindcss()],
  },
});
