import { M } from "../Math";

export function Header() {
  return (
    <header className="prose-col pt-20 pb-4 md:pt-28">
      <p
        className="sc-label text-[0.8rem] mb-8"
        style={{ color: "var(--ink-faint)" }}
      >
        machine-checked mathematics &middot; lean 4 &middot; june 2026
      </p>
      <h1
        className="text-[2rem] md:text-[2.6rem] font-semibold leading-[1.15]"
        style={{ letterSpacing: "-0.015em" }}
      >
        Pinning <M>{String.raw`\delta^*`}</M>: Machine-Checked Thresholds for
        Mutual Correlated Agreement of Reed&ndash;Solomon Codes
      </h1>
      <p className="mt-7 text-[1.02rem]" style={{ color: "var(--ink-secondary)" }}>
        The ArkLib <M>{String.raw`\delta^*`}</M> campaign &middot; an LLM agent
        fleet writing Lean&nbsp;4, verified by the Lean kernel
      </p>
      <p className="mt-2 text-[0.9rem]" style={{ color: "var(--ink-faint)" }}>
        <a href="https://github.com/lalalune/ArkLib">lalalune/ArkLib</a>
        {" "}&middot;{" "}
        <a href="https://github.com/lalalune/ArkLib/issues/371">
          campaign log: issues #232 &rarr; #334 &rarr; #357 &rarr; #371
        </a>
      </p>
      <div
        className="mt-10 mb-2 h-px w-full"
        style={{ background: "var(--rule)" }}
      />
    </header>
  );
}
