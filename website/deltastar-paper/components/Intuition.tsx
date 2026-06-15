import type { ReactNode } from "react";

/**
 * An academic "Intuition" aside: a sober, plain-language gloss for a
 * non-specialist reader. Rendered as an understated left-ruled callout in the
 * serif body. No popup, no toggle, no marketing register.
 */
export function Intuition({ children }: { children: ReactNode }) {
  return (
    <aside
      className="my-6 border-l-2 pl-4 py-1 text-[0.93rem] leading-relaxed"
      style={{
        borderColor: "var(--rule, rgba(0,0,0,0.18))",
        color: "var(--ink-faint, #555)",
      }}
    >
      <span
        className="sc-label mr-2 font-semibold uppercase tracking-wide text-[0.7rem]"
        style={{ color: "var(--ink-secondary, #333)" }}
      >
        Intuition
      </span>
      {children}
    </aside>
  );
}
