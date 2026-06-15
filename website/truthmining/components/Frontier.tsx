/* The verifier frontier. Honest map of which domains have a cheap trustless
   check today. Naming the boundary is the credibility. */

type Tier = {
  domain: string;
  verifier: string;
  grade: "perfect" | "good" | "approx" | "none";
  note: string;
  tag?: string;
};

const TIERS: Tier[] = [
  {
    domain: "Formal mathematics",
    verifier: "Lean / Coq / Isabelle kernel",
    grade: "perfect",
    note: "Checks in milliseconds. Zero trust in the producer. The beachhead, and it is not close.",
    tag: "beachhead",
  },
  {
    domain: "Cryptography & security",
    verifier: "contract proofs · test vectors · differential fuzzing",
    grade: "good",
    note: "Cheap and largely trustless. Real buyers, real budgets. This is where the revenue is.",
    tag: "the commercial step",
  },
  {
    domain: "Computational biology",
    verifier: "energy validation · docking · in-silico assays",
    grade: "approx",
    note: "Cheap but approximate. Certified candidates, not proofs.",
  },
  {
    domain: "Most empirical science",
    verifier: "the universe, billed by the week",
    grade: "none",
    note: "No cheap verifier. Ground truth needs an experiment. Not minable today.",
  },
];

const GRADE: Record<
  Tier["grade"],
  { label: string; color: string; fill: number; chip: string }
> = {
  perfect: { label: "perfect", color: "var(--ok)", fill: 100, chip: "chip-ok" },
  good: { label: "good", color: "var(--ok-dim)", fill: 74, chip: "" },
  approx: { label: "approximate", color: "var(--no)", fill: 46, chip: "chip-no" },
  none: { label: "not yet", color: "var(--noise)", fill: 16, chip: "" },
};

export function Frontier() {
  return (
    <div className="brick overflow-hidden">
      {TIERS.map((t, i) => {
        const g = GRADE[t.grade];
        return (
          <div
            key={t.domain}
            className="relative"
            style={{
              borderTop: i === 0 ? "none" : "1px solid var(--rule-faint)",
              padding: "clamp(1.1rem, 3vw, 1.6rem)",
            }}
          >
            {/* fill bar showing verifier strength */}
            <div
              className="absolute left-0 top-0 bottom-0 pointer-events-none"
              style={{
                width: `${g.fill}%`,
                background: `linear-gradient(90deg, ${
                  t.grade === "perfect"
                    ? "var(--ok-soft)"
                    : t.grade === "approx"
                    ? "var(--no-soft)"
                    : "var(--rule-faint)"
                }, transparent)`,
              }}
            />
            <div className="relative flex flex-col md:flex-row md:items-baseline gap-2 md:gap-6">
              <div className="md:w-56 flex-none">
                <h3 className="text-[1.05rem]" style={{ fontWeight: 600 }}>
                  {t.domain}
                </h3>
                <div className="flex flex-wrap items-center gap-2 mt-2">
                  <span
                    className={`chip ${g.chip}`}
                    style={!g.chip ? { color: g.color, borderColor: "var(--rule)" } : undefined}
                  >
                    <span className="dot" style={{ background: g.color }} />
                    {g.label}
                  </span>
                  {t.tag ? (
                    <span
                      className="mono text-[0.6rem] uppercase"
                      style={{ letterSpacing: "0.12em", color: "var(--ink-faint)" }}
                    >
                      {t.tag}
                    </span>
                  ) : null}
                </div>
              </div>
              <div className="flex-1">
                <p className="mono text-[0.74rem] mb-1.5" style={{ color: "var(--ink-3)" }}>
                  {t.verifier}
                </p>
                <p className="text-[0.92rem]" style={{ color: "var(--ink-2)" }}>
                  {t.note}
                </p>
              </div>
            </div>
          </div>
        );
      })}
    </div>
  );
}
