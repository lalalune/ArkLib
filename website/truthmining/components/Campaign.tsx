/* The campaign flow. The product is not "a result". It is a delivery unit.
   Client gives a target + a PRE-COMMITTED acceptance criterion + a fee.
   The criterion is frozen before the fleet runs, so the proof cannot be moved
   to meet the output. Deliverable = a repo + a one-command re-verification.

   The one motion idea lives here: the acceptance criterion visibly LOCKS
   (freezes) before the fleet runs, and at the end the re-verify command
   resolves green. CSS-only, deterministic, reduced-motion safe. */

const STEPS = [
  {
    n: "01",
    k: "you commit",
    t: "A formal target",
    d: "A proposition in Lean 4 that must hold. Provable, refutable, or reducible to a named lemma.",
  },
  {
    n: "02",
    k: "you commit",
    t: "An acceptance criterion, frozen",
    d: "The exact Lean signature that must typecheck, plus the axiom budget. Locked before the fleet starts.",
    locks: true,
  },
  {
    n: "03",
    k: "you commit",
    t: "A fee or bounty",
    d: "A campaign fee, a success bounty, or both. Agreed up front.",
  },
];

export function Campaign() {
  return (
    <div className="grid gap-3">
      {/* the three client inputs */}
      <div className="grid sm:grid-cols-3 gap-3">
        {STEPS.map((s) => (
          <div
            key={s.n}
            className="brick p-5 relative overflow-hidden flex flex-col"
            style={s.locks ? { borderColor: "rgba(89, 230, 160, 0.28)" } : undefined}
          >
            <div className="flex items-center justify-between mb-3">
              <span className="mono text-[0.7rem]" style={{ color: "var(--ink-3)" }}>
                {s.n}
              </span>
              <span className="mono text-[0.6rem] uppercase" style={{ letterSpacing: "0.14em", color: "var(--ink-faint)" }}>
                {s.k}
              </span>
            </div>
            <p className="text-[1.0rem] mb-2" style={{ fontWeight: 600 }}>
              {s.t}
            </p>
            <p className="text-[0.88rem]" style={{ color: "var(--ink-2)", lineHeight: 1.5 }}>
              {s.d}
            </p>
            {s.locks ? (
              <div
                className="mt-3 pt-3 flex items-center gap-2 mono text-[0.66rem]"
                style={{ borderTop: "1px solid var(--rule-faint)" }}
              >
                <span className="freeze-dot" />
                <span className="freeze-label" style={{ color: "var(--ink-3)" }}>
                  criterion frozen
                </span>
              </div>
            ) : null}
          </div>
        ))}
      </div>

      {/* arrow down into the fleet */}
      <div className="flex items-center justify-center py-1" aria-hidden="true">
        <span className="mono text-[0.8rem]" style={{ color: "var(--ink-faint)" }}>
          ↓ the fleet runs · the kernel gates every brick · the audit-guard hunts false positives
        </span>
      </div>

      {/* the deliverable: the buyer trusts nothing, they run the command */}
      <div className="brick brick-ok p-6 sm:p-7">
        <div className="flex items-center justify-between mb-5 flex-wrap gap-3">
          <span className="chip chip-ok">
            <span className="dot" /> deliverable
          </span>
          <span className="mono text-[0.7rem]" style={{ color: "var(--ink-3)" }}>
            you trust nothing · you run the command
          </span>
        </div>

        {/* terminal block: the re-verify resolves green */}
        <div
          className="rounded-lg p-4 sm:p-5 mono text-[0.78rem] leading-relaxed overflow-x-auto"
          style={{ background: "var(--bg-sunk)", border: "1px solid var(--rule)" }}
        >
          <p style={{ color: "var(--ink-3)" }}>
            <span style={{ color: "var(--ink-faint)" }}>$</span> lake exe verify
          </p>
          <p className="verify-line" style={{ color: "var(--ok)" }}>
            ✓ target signature typechecks · pinned toolchain · kernel clean
          </p>
          <p style={{ color: "var(--ink-3)", marginTop: "0.6em" }}>
            <span style={{ color: "var(--ink-faint)" }}>$</span> lake exe census
          </p>
          <p className="verify-line verify-line-2" style={{ color: "var(--ok)" }}>
            ✓ #print axioms · trust base = Mathlib only · nothing smuggled in
          </p>
        </div>

        <div className="grid sm:grid-cols-3 gap-4 mt-6">
          {[
            ["a Lean repo", "the target signature typechecks against a pinned toolchain"],
            ["one-command re-verify", "green or red, from clean, on your machine"],
            ["an axiom census", "#print axioms, so the trust base is Mathlib and nothing else"],
          ].map(([h, d]) => (
            <div key={h}>
              <p className="mono text-[0.78rem] mb-1" style={{ color: "var(--ok)" }}>
                {h}
              </p>
              <p className="text-[0.86rem]" style={{ color: "var(--ink-2)", lineHeight: 1.45 }}>
                {d}
              </p>
            </div>
          ))}
        </div>
      </div>
    </div>
  );
}
