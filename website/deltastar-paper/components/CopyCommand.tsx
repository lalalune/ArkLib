"use client";

import { useState } from "react";

/**
 * A shell command rendered as a click-to-copy block. Keeps the site static
 * (no runtime deps) — the only client interactivity on the page besides the
 * degen toggle. The displayed text and the copied text are the same string.
 */
export function CopyCommand({ command }: { command: string }) {
  const [copied, setCopied] = useState(false);

  function copy() {
    navigator.clipboard?.writeText(command).then(
      () => {
        setCopied(true);
        window.setTimeout(() => setCopied(false), 1500);
      },
      () => {},
    );
  }

  return (
    <button
      type="button"
      className="cmd"
      onClick={copy}
      aria-label={`Copy command: ${command}`}
    >
      <code>{command}</code>
      <span className="cmd-copy" aria-hidden>
        {copied ? "copied ✓" : "copy"}
      </span>
    </button>
  );
}
