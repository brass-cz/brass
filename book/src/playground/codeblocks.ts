/// Make the docs' prepoly code blocks executable: every rendered
/// ```prepoly fence gets a Run button that feeds the block's source to the
/// wasm interpreter and prints stdout/stderr beneath the block. The code text
/// comes from Expressive Code's copy button (`data-code`, newlines encoded as
/// U+007F), falling back to the block's text content.

import { runProgram } from "./run";
import "./codeblocks.css";

const codeOf = (figure: Element): string => {
  const button = figure.querySelector<HTMLButtonElement>("button[data-code]");
  if (button?.dataset.code) {
    return button.dataset.code.replaceAll("\u007f", "\n");
  }
  return figure.querySelector("pre")?.textContent ?? "";
};

const attachRunButton = (block: HTMLElement) => {
  const figure = block.querySelector("figure.frame");
  if (!figure) return;

  const controls = document.createElement("div");
  controls.className = "pp-run";

  const button = document.createElement("button");
  button.type = "button";
  button.className = "pp-run-button";
  button.textContent = "▶ Run";

  const output = document.createElement("div");
  output.className = "pp-run-output";
  output.hidden = true;
  const stdout = document.createElement("pre");
  stdout.className = "pp-run-stdout";
  const stderr = document.createElement("pre");
  stderr.className = "pp-run-stderr";
  output.append(stdout, stderr);

  button.addEventListener("click", async () => {
    button.disabled = true;
    button.textContent = "Running…";
    stdout.textContent = "";
    stderr.textContent = "";
    output.hidden = false;
    try {
      await runProgram(
        codeOf(figure),
        (line) => {
          stdout.textContent += line + "\n";
        },
        (line) => {
          stderr.textContent += line + "\n";
        },
      );
      if (!stdout.textContent && !stderr.textContent) {
        stdout.textContent = "(no output)";
      }
    } catch (err) {
      stderr.textContent += String(err) + "\n";
    } finally {
      button.disabled = false;
      button.textContent = "▶ Run";
    }
  });

  controls.append(button, output);
  // Insert after the Expressive Code container, not inside it: EC resets its
  // descendants with `all: revert`, which cancels the `hidden` attribute's
  // presentational display:none and would keep the empty output box visible.
  block.after(controls);
};

export const attachRunButtons = () => {
  for (const block of document.querySelectorAll<HTMLElement>(
    "div.expressive-code",
  )) {
    if (
      block.querySelector('pre[data-language="prepoly"]') &&
      !block.querySelector("[data-norun]")
    ) {
      attachRunButton(block);
    }
  }
};
