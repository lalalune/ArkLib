/* The moat, stated honestly. It is not the miners. Those are rented LLMs and
   they commoditize. It is the audit-guard (hunts false positives, caught real
   bugs in the delta-star campaign) and the verifier frontier (knowing how to
   turn a domain's correctness question into a cheap trustless check). */

export function Moat() {
  return (
    <div className="grid gap-3">
      <div className="grid lg:grid-cols-2 gap-3">
        {/* the audit-guard: the crown jewel */}
        <div className="brick brick-ok p-6 sm:p-7 flex flex-col">
          <span className="chip chip-ok mb-4">
            <span className="dot" /> the audit-guard
          </span>
          <h3 className="text-[1.25rem] mb-3" style={{ fontWeight: 600 }}>
            The kernel says yes. The audit-guard asks: to the thing we wanted?
          </h3>
          <p className="text-[0.96rem]" style={{ color: "var(--ink-2)", lineHeight: 1.55 }}>
            A meta-checker that hunts false positives: bricks that typecheck but
            prove something weaker, vacuous statements, signatures that drifted
            from the criterion. It caught real bugs in the{" "}
            <span style={{ color: "var(--ink)" }}>δ*</span> campaign. The
            difference between a kernel-green lie and a mined truth.
          </p>
        </div>

        {/* the verifier frontier playbook */}
        <div className="brick p-6 sm:p-7 flex flex-col">
          <span className="chip mb-4" style={{ color: "var(--ink)", borderColor: "var(--rule-strong)" }}>
            <span className="dot" /> the verifier frontier
          </span>
          <h3 className="text-[1.25rem] mb-3" style={{ fontWeight: 600 }}>
            Knowing what is mineable, and how to check it.
          </h3>
          <p className="text-[0.96rem]" style={{ color: "var(--ink-2)", lineHeight: 1.55 }}>
            Turning a domain&#8217;s correctness question into a cheap trustless
            check is the rare skill. The orchestration, the honesty contract
            that bans <span className="code">native_decide</span>,{" "}
            <span className="code">sorry</span> and unaudited axioms, and the
            catalog of solved targets all compound.
          </p>
        </div>
      </div>

      {/* the honest part: miners commoditize */}
      <div className="brick p-6 flex flex-col sm:flex-row sm:items-center gap-5">
        <span className="chip chip-no flex-none">
          <span className="dot" /> said plainly
        </span>
        <p className="text-[0.96rem]" style={{ color: "var(--ink-2)", lineHeight: 1.55 }}>
          The miners are rented LLMs and they commoditize. Anyone can point a
          frontier model at Lean. The moat is the audit-guard, the frontier
          playbook, and a public re-checkable track record. The assets that
          survive smarter miners.
        </p>
      </div>
    </div>
  );
}
