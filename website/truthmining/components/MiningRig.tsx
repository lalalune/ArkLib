/* The one memorable motion idea.
   A small fleet of candidate proofs. Hash-noise scrambles in each cell; on a
   staggered cadence, a cell "resolves": its hash fades and a kernel-checked
   line locks in green. One brick at a time, like a rig finding a block.
   Pure CSS keyframes. Deterministic. Honors prefers-reduced-motion. */

const HASH = "0xa7f3c91e";

type Cell = {
  // the line that locks in when verified
  proof: string;
  // refutation cells show amber "not provable" honesty
  refuted?: boolean;
  delay: number;
};

const CELLS: Cell[] = [
  { proof: "lemma decoupling := by", delay: 0.0 },
  { proof: "theorem sub_johnson", delay: 1.4 },
  { proof: "¬ conjecture_A", refuted: true, delay: 2.1 },
  { proof: "lemma window_pin := by", delay: 0.7 },
  { proof: "theorem ceiling_exact", delay: 2.8 },
  { proof: "audit_guard.passed", delay: 1.05 },
  { proof: "¬ floor_naive", refuted: true, delay: 3.2 },
  { proof: "lemma agreement := by", delay: 0.35 },
  { proof: "theorem decouple_field", delay: 2.45 },
];

export function MiningRig() {
  return (
    <div
      className="brick relative overflow-hidden"
      style={{ padding: "clamp(0.9rem, 2.5vw, 1.4rem)" }}
      aria-hidden="true"
    >
      {/* header strip: looks like a rig dashboard */}
      <div className="flex items-center justify-between mb-4">
        <span className="eyebrow" style={{ letterSpacing: "0.18em" }}>
          fleet · lean 4 kernel
        </span>
        <span className="chip chip-ok">
          <span className="dot" /> verifier online
        </span>
      </div>

      {/* scanning line */}
      <div
        className="pointer-events-none absolute left-0 right-0"
        style={{
          top: 0,
          height: "42%",
          background:
            "linear-gradient(180deg, transparent, var(--ok-soft), transparent)",
          animation: "scan 6s cubic-bezier(0.4,0,0.2,1) infinite",
        }}
      />

      <div
        className="grid gap-2"
        style={{ gridTemplateColumns: "repeat(3, minmax(0,1fr))" }}
      >
        {CELLS.map((c, i) => (
          <div
            key={i}
            className="mono relative rounded-md px-2.5 py-3 text-[0.62rem] leading-tight overflow-hidden"
            style={{
              border: "1px solid var(--rule)",
              background: "var(--bg-sunk)",
              minHeight: "3.1rem",
              animation: c.refuted
                ? undefined
                : `lock-in 6s ease-in-out ${c.delay}s infinite`,
            }}
          >
            {/* hash noise that fades out as the proof resolves */}
            <span
              className="absolute inset-0 flex items-center justify-center"
              style={{
                color: "var(--noise)",
                letterSpacing: "0.05em",
                animation: `hash-fade 6s ease-in-out ${c.delay}s infinite`,
              }}
            >
              <span
                style={{
                  animation: `scramble 0.9s steps(2) ${i * 0.13}s infinite`,
                }}
              >
                {HASH}
              </span>
            </span>

            {/* the verified line */}
            <span
              className="absolute inset-0 flex items-center px-2.5"
              style={{
                color: c.refuted ? "var(--no)" : "var(--ok)",
                animation: `flip-true 6s ease-in-out ${c.delay}s infinite`,
              }}
            >
              <span className="truncate">
                {c.refuted ? "✕ " : "✓ "}
                {c.proof}
              </span>
            </span>
          </div>
        ))}
      </div>

      <div
        className="flex items-center justify-between mt-4 pt-3 text-[0.66rem] mono"
        style={{ borderTop: "1px solid var(--rule-faint)", color: "var(--ink-3)" }}
      >
        <span>~150 bricks mined</span>
        <span style={{ color: "var(--ok)" }}>every accepted result typechecks</span>
      </div>
    </div>
  );
}
