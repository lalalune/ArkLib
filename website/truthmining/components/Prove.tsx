/* What we actually prove, for money. The headline prize is the lead magnet;
   the business is formal verification of crypto code. Buyers already pay
   human FV shops $25-500k. A kernel-checked proof is a strictly better
   artifact than a PDF of findings. Market price ranges are public context,
   not our prices. */

type Product = {
  k: string;
  t: string;
  spec: string;
  d: string;
};

const PRODUCTS: Product[] = [
  {
    k: "zk circuit soundness",
    t: "ZK circuit soundness proofs",
    spec: "extracted circuit refines the spec · no under-constrained signals",
    d: "Proof that the circuit means what the spec says, kernel-checked. ZK bugs are critical and the experts are scarce.",
  },
  {
    k: "contract invariants",
    t: "Smart-contract invariant proofs",
    spec: "no-bad-debt · conservation-of-supply · monotone accounting",
    d: "The properties that must hold for every state, not just the fuzzed ones. Write the invariant, the kernel settles it.",
  },
];

export function Prove() {
  return (
    <div className="grid gap-3">
      <div className="grid md:grid-cols-2 gap-3">
        {PRODUCTS.map((p) => (
          <div key={p.k} className="brick p-6 flex flex-col">
            <span className="mono text-[0.66rem] uppercase mb-4" style={{ letterSpacing: "0.14em", color: "var(--ok)" }}>
              {p.k}
            </span>
            <h3 className="text-[1.2rem] mb-3" style={{ fontWeight: 600 }}>
              {p.t}
            </h3>
            <div
              className="rounded-md px-3 py-2 mono text-[0.72rem] mb-4"
              style={{ background: "var(--bg-sunk)", border: "1px solid var(--rule-faint)", color: "var(--ink-3)" }}
            >
              acceptance: {p.spec}
            </div>
            <p className="text-[0.94rem]" style={{ color: "var(--ink-2)", lineHeight: 1.5 }}>
              {p.d}
            </p>
          </div>
        ))}
      </div>

      {/* the artifact comparison + market context */}
      <div className="grid lg:grid-cols-[1.1fr_0.9fr] gap-3">
        <div className="brick p-6 flex flex-col justify-center">
          <p className="eyebrow mb-4">a strictly better artifact</p>
          <div className="grid grid-cols-2 gap-px">
            <div className="pr-5">
              <p className="mono text-[0.74rem] mb-2" style={{ color: "var(--ink-3)" }}>
                human FV shop ships
              </p>
              <p className="text-[1.0rem]" style={{ color: "var(--no)" }}>
                a PDF of findings
              </p>
              <p className="text-[0.84rem] mt-2" style={{ color: "var(--ink-3)" }}>
                you trust the reviewer
              </p>
            </div>
            <div className="pl-5" style={{ borderLeft: "1px solid var(--rule)" }}>
              <p className="mono text-[0.74rem] mb-2" style={{ color: "var(--ink-3)" }}>
                a campaign ships
              </p>
              <p className="text-[1.0rem]" style={{ color: "var(--ok)" }}>
                a re-checkable proof
              </p>
              <p className="text-[0.84rem] mt-2" style={{ color: "var(--ink-3)" }}>
                you trust the kernel
              </p>
            </div>
          </div>
        </div>

        <div className="brick p-6 flex flex-col justify-center">
          <p className="eyebrow mb-4">market context · what buyers pay humans</p>
          <ul className="grid gap-2.5">
            {[
              ["contract FV, simple", "$5–15k"],
              ["DeFi protocol FV", "$20–60k"],
              ["complex / ZK systems", "$80–150k"],
              ["enterprise", "$250–500k"],
            ].map(([label, price]) => (
              <li key={label} className="flex items-baseline justify-between gap-4">
                <span className="text-[0.9rem]" style={{ color: "var(--ink-2)" }}>
                  {label}
                </span>
                <span className="mono text-[0.86rem] stat-num" style={{ color: "var(--ink)" }}>
                  {price}
                </span>
              </li>
            ))}
          </ul>
          <p className="mono text-[0.66rem] mt-4" style={{ color: "var(--ink-faint)", lineHeight: 1.5 }}>
            public FV-market ranges. not our prices.
          </p>
        </div>
      </div>
    </div>
  );
}
