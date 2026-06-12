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
        className="text-[2.4rem] md:text-[3.2rem] font-semibold leading-[1.08]"
        style={{ letterSpacing: "-0.02em" }}
      >
        The Million-Dollar Window
      </h1>
      <p
        className="mt-6 text-[1.15rem] leading-[1.5]"
        style={{ color: "var(--ink-secondary)" }}
      >
        What happened when a swarm of AI agents attacked one of
        Ethereum&rsquo;s hardest open math problems, with a proof checker as
        referee.
      </p>
      <p className="mt-6 text-[0.9rem]" style={{ color: "var(--ink-faint)" }}>
        A campaign report on the mutual correlated agreement threshold{" "}
        <M>{String.raw`\delta^*`}</M> for smooth Reed&ndash;Solomon codes
        &middot; the ArkLib <M>{String.raw`\delta^*`}</M> campaign &middot; an
        LLM agent fleet writing Lean&nbsp;4, verified by the Lean kernel
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
