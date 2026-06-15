import { M } from "../Math";

export function Header() {
  return (
    <header className="prose-col pt-20 pb-4 md:pt-28">
      <p
        className="sc-label text-[0.8rem] mb-8"
        style={{ color: "var(--ink-faint)" }}
      >
        Machine-checked mathematics &middot; Lean 4 &middot; June 2026
      </p>
      <h1
        className="text-[2.1rem] md:text-[2.7rem] font-semibold leading-[1.12]"
        style={{ letterSpacing: "-0.018em" }}
      >
        Pinning <M>{String.raw`\delta^*`}</M>: Machine-Checked Thresholds for
        Mutual Correlated Agreement of Smooth Reed&ndash;Solomon Codes
      </h1>
      <p
        className="mt-6 text-[1.05rem] leading-[1.5]"
        style={{ color: "var(--ink-secondary)" }}
      >
        A formal-verification study of the mutual correlated agreement threshold{" "}
        <M>{String.raw`\delta^*`}</M> for smooth-domain Reed&ndash;Solomon
        codes, conducted in Lean&nbsp;4 over the ArkLib library. We isolate the
        field-dependent part of the threshold from the purely combinatorial
        part, and state precisely what is proven, what is computed, and what
        remains open.
      </p>
      <p className="mt-6 text-[0.9rem]" style={{ color: "var(--ink-faint)" }}>
        The ArkLib <M>{String.raw`\delta^*`}</M> formalization effort, led by{" "}
        <a href="https://github.com/lalalune">Shaw</a> &middot;{" "}
        <a href="https://github.com/lalalune/ArkLib">lalalune/ArkLib</a>
      </p>
      <div className="mt-8 flex flex-wrap items-center gap-3">
        <a
          href="/deltastar.pdf"
          className="inline-flex items-center gap-2 rounded-md px-4 py-2 text-[0.92rem] font-semibold no-underline"
          style={{ background: "var(--accent)", color: "var(--bg)" }}
        >
          <span aria-hidden>&darr;</span> Download PDF
        </a>
        <span className="text-[0.82rem]" style={{ color: "var(--ink-faint)" }}>
          the full machine-checked write-up
        </span>
      </div>
      <div
        className="mt-10 mb-2 h-px w-full"
        style={{ background: "var(--rule)" }}
      />
    </header>
  );
}
