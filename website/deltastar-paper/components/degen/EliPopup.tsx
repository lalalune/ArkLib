"use client";

import { useEffect, useState } from "react";
import { useDegen } from "./DegenProvider";

export function EliPopup() {
  const { degen, toggle } = useDegen();
  const [show, setShow] = useState(false);
  const [dismissed, setDismissed] = useState(false);

  useEffect(() => {
    try {
      if (sessionStorage.getItem("deltastar-eli-dismissed") === "1") {
        setDismissed(true);
        return;
      }
    } catch {}
    let fired = false;
    const onScroll = () => {
      if (fired) return;
      const doc = document.documentElement;
      const depth =
        window.scrollY / Math.max(1, doc.scrollHeight - window.innerHeight);
      if (depth > 0.2) {
        fired = true;
        setShow(true);
        window.removeEventListener("scroll", onScroll);
      }
    };
    window.addEventListener("scroll", onScroll, { passive: true });
    return () => window.removeEventListener("scroll", onScroll);
  }, []);

  const dismiss = () => {
    setShow(false);
    setDismissed(true);
    try {
      sessionStorage.setItem("deltastar-eli-dismissed", "1");
    } catch {}
  };

  return (
    <>
      {/* the popup */}
      <div
        aria-hidden={!show}
        className="fixed inset-x-0 bottom-0 z-50 flex justify-center px-4 pb-5 pointer-events-none"
        style={{
          transform: show ? "translateY(0)" : "translateY(120%)",
          transition: "transform 0.55s cubic-bezier(0.16, 1.3, 0.3, 1)",
        }}
      >
        <div
          className="pointer-events-auto w-full max-w-xl rounded-lg border px-6 py-5 shadow-2xl"
          style={{
            background: "var(--paper-raised)",
            borderColor: "var(--rule)",
            boxShadow:
              "0 12px 40px rgba(0,0,0,0.18), 0 2px 8px rgba(0,0,0,0.08)",
          }}
        >
          <p className="text-[1.02rem] font-medium" style={{ color: "var(--ink)" }}>
            This shit is too complex. Can you explain it to me like I&rsquo;m a
            retard?
          </p>
          <div className="mt-4 flex flex-wrap gap-3">
            <button
              onClick={() => {
                if (!degen) toggle();
                dismiss();
              }}
              className="rounded-md px-4 py-2 text-[0.92rem] font-semibold cursor-pointer"
              style={{ background: "var(--accent)", color: "var(--paper)" }}
            >
              yes. dumb it down
            </button>
            <button
              onClick={dismiss}
              className="rounded-md border px-4 py-2 text-[0.92rem] cursor-pointer"
              style={{ borderColor: "var(--rule)", color: "var(--ink-secondary)" }}
            >
              no, I have a PhD in coding theory
            </button>
          </div>
        </div>
      </div>

      {/* persistent pill after first contact */}
      {(dismissed || degen) && (
        <button
          onClick={toggle}
          className="fixed bottom-4 right-4 z-40 rounded-full border px-3.5 py-2 font-mono text-[0.78rem] cursor-pointer shadow-lg"
          style={{
            background: degen ? "var(--accent)" : "var(--paper-raised)",
            color: degen ? "var(--paper)" : "var(--ink-secondary)",
            borderColor: degen ? "var(--accent)" : "var(--rule)",
          }}
          title="toggle degen translation mode"
        >
          {degen ? "degen mode: ON" : "🧠→🥴 degen mode"}
        </button>
      )}
    </>
  );
}
