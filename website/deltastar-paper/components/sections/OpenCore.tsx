import { Section, SubSection } from "../Section";
import { Intuition } from "../Intuition";
import { M, MD } from "../Math";
import { Theorem } from "../Theorem";

function CrossingFigure() {
  const stroke = "var(--ink-secondary)";
  const accent = "var(--accent)";
  const faint = "var(--ink-faint)";
  // I(s) for n=24,k=2 (exact in-tree curve), log scale
  const data: [number, number][] = [
    [4, 361], [5, 71], [6, 40], [7, 24], [8, 18], [9, 15], [10, 15], [11, 5], [12, 5], [13, 5],
  ];
  const x0 = 56, x1 = 600, y0 = 30, y1 = 250;
  const sMin = 4, sMax = 13;
  const lyMin = Math.log10(3), lyMax = Math.log10(600);
  const X = (s: number) => x0 + ((s - sMin) / (sMax - sMin)) * (x1 - x0);
  const Y = (v: number) =>
    y1 - ((Math.log10(v) - lyMin) / (lyMax - lyMin)) * (y1 - y0);
  const path = data.map(([s, v], i) => `${i ? "L" : "M"} ${X(s)} ${Y(v)}`).join(" ");
  return (
    <figure className="prose-col my-10">
      <svg viewBox="0 0 640 300" className="w-full" role="img"
        aria-label="Incidence decay I(s) against two budget normalizations">
        {/* axes */}
        <line x1={x0} y1={y1} x2={x1 + 16} y2={y1} stroke={stroke} strokeWidth="1.2" />
        <line x1={x0} y1={y0 - 6} x2={x0} y2={y1} stroke={stroke} strokeWidth="1.2" />
        {/* budget = n = 24 (log10 ~1.38) */}
        <line x1={x0} y1={Y(24)} x2={x1} y2={Y(24)} stroke={accent} strokeWidth="1.3" strokeDasharray="6 4" />
        <text x={x1 - 4} y={Y(24) - 6} textAnchor="end" fontSize="11" fill={accent}>budget B = n</text>
        {/* budget ~ n^{3-eps} (floor), illustrative at ~300 */}
        <line x1={x0} y1={Y(300)} x2={x1} y2={Y(300)} stroke="var(--ink-secondary)" strokeWidth="1.1" strokeDasharray="2 4" />
        <text x={x1 - 4} y={Y(300) - 6} textAnchor="end" fontSize="11" fill={stroke}>
          budget ~ n^(3-ε) (floor)
        </text>
        {/* I(s) curve */}
        <path d={path} fill="none" stroke={stroke} strokeWidth="1.8" />
        {data.map(([s, v]) => (
          <circle key={s} cx={X(s)} cy={Y(v)} r="3" fill={stroke} />
        ))}
        {/* x ticks */}
        {[4, 6, 8, 10, 12].map((s) => (
          <g key={s}>
            <line x1={X(s)} y1={y1} x2={X(s)} y2={y1 + 5} stroke={stroke} strokeWidth="1" />
            <text x={X(s)} y={y1 + 18} textAnchor="middle" fontSize="11" fill={faint}>{s}</text>
          </g>
        ))}
        <text x={(x0 + x1) / 2} y={y1 + 34} textAnchor="middle" fontSize="12" fill={stroke}>
          witness size s &nbsp;(radius δ = 1 − s/n)
        </text>
        <text x={x0 - 40} y={(y0 + y1) / 2} fontSize="12" fill={stroke}
          transform={`rotate(-90 ${x0 - 40} ${(y0 + y1) / 2})`} textAnchor="middle">
          I(s) (log scale)
        </text>
      </svg>
      <figcaption className="text-[0.85rem] mt-3" style={{ color: "var(--ink-faint)" }}>
        Incidence decay <M>{String.raw`I(s)`}</M> (exact, <M>{String.raw`n=24,\,k=2`}</M>) against two
        budget normalizations. The windowed budget <M>{String.raw`B=n`}</M> crosses near{" "}
        <M>{String.raw`s^*\approx n/2`}</M>, giving <M>{String.raw`\delta^*\to\tfrac12`}</M>. The
        conjectured floor requires the crossing at <M>{String.raw`s^*-k=\Theta(n/\log n)`}</M>, i.e.\ a
        super-linear budget. Whether the prize budget <M>{String.raw`\varepsilon^* q`}</M> realizes that
        crossing is the central open problem.
      </figcaption>
    </figure>
  );
}

export function OpenCore() {
  return (
    <Section id="open-core" num="5" title="The floor reduces to a budget crossing">
      <Intuition>After the decoupling, whether delta-star reaches its conjectured value comes down to a single clean question: does the security budget cross a known incidence-count curve at a particular witness size? This is a finite, analysis-free question. We state it precisely and do not claim to settle it; it is the central open problem this work leaves.</Intuition>
      <p>
        The decoupling converts the floor question into a statement about one
        curve and one budget, with no character-sum input. Let{" "}
        <M>{String.raw`I(s)`}</M> denote the over-determined far-line incidence
        maximum as a function of witness size <M>{String.raw`s`}</M>, in the
        regime where Theorem&nbsp;3.1 applies (so <M>{String.raw`I(s)`}</M> is{" "}
        <M>{String.raw`p`}</M>-independent).
      </p>

      <CrossingFigure />

      <p>
        In the <M>{String.raw`p`}</M>-independent over-determined regime,{" "}
        <M>{String.raw`\delta^*=(n-s^*)/n`}</M> where{" "}
        <M>{String.raw`s^*=\min\{s: I(s)\le B\}`}</M> is the budget crossing,
        with <M>{String.raw`B=q\varepsilon^*`}</M>. Consequently{" "}
        <M>{String.raw`\delta^*`}</M> is monotone in the budget normalization:
      </p>
      <MD>{String.raw`B\sim n\ \Rightarrow\ \delta^*\to\tfrac12;\qquad B\sim n^{3-\epsilon}\ \Rightarrow\ \delta^*\to1-\rho-\Theta(1/\log n);\qquad B\sim n^3\ \Rightarrow\ \delta^*\to1-\rho.`}</MD>

      <div className="my-8 rounded-md p-5"
        style={{ border: "1px solid var(--rule)", background: "var(--surface, transparent)" }}>
        <p className="sc-label text-[0.8rem] font-semibold mb-2"
          style={{ color: "var(--accent)" }}>
          Open Problem 5.1: the floor crossing
        </p>
        <p className="m-0">
          In the prize regime <M>{String.raw`\varepsilon^*=2^{-128}`}</M>,{" "}
          <M>{String.raw`q=n^\beta`}</M> with{" "}
          <M>{String.raw`\beta\approx4\text{--}5`}</M>, the budget is{" "}
          <M>{String.raw`B=q\varepsilon^*=2^{-128}n^\beta`}</M>, super-linear in{" "}
          <M>{String.raw`n`}</M>. Does this budget cross{" "}
          <M>{String.raw`I(s)`}</M> at witness size{" "}
          <M>{String.raw`s^*-k=\Theta(n/\log n)`}</M>, thereby pinning the floor
          at <M>{String.raw`\delta^*=1-\rho-\Theta(1/\log n)`}</M>? Equivalently:
          derive the full <M>{String.raw`s`}</M>-dependence of{" "}
          <M>{String.raw`I(s)`}</M> and locate the crossing of{" "}
          <M>{String.raw`B=q\varepsilon^*`}</M>.
        </p>
      </div>

      <p>
        Open Problem&nbsp;5.1 is <em>purely combinatorial</em>: by Theorem&nbsp;3.1
        the curve <M>{String.raw`I(s)`}</M> is{" "}
        <M>{String.raw`p`}</M>-independent, so neither the crossing location nor
        the resulting <M>{String.raw`\delta^*`}</M> requires any estimate on the
        Gauss sum <M>{String.raw`M(n)`}</M>. This is the entire value of the
        decoupling, and it is also its limit. We emphasize, to avoid any
        overstatement: <strong>the decoupling does not establish that the floor
        attains its conjectured value.</strong> It establishes that doing so
        reduces to the budget-versus-decay crossing above, and that this crossing
        involves no character-sum analysis. The crossing condition is open. We
        make no claim that it holds.
      </p>

      <SubSection num="5.1" title="The window does not decouple">
        <p>
          The decoupling is an over-determined / boundary phenomenon. It is
          important to state, equally precisely, what it does <em>not</em> buy:
          the threshold strictly inside the window remains tied to the BGK wall.
        </p>
        <Theorem
          kind="Proposition"
          name="Window re-coupling to the moment"
          file="Frontier/_MomentMethodNoGo.lean"
          decl="probe N10, computational"
          conditional="exact computation, n ∈ {8,16,32}"
        >
          <p className="m-0">
            <strong>(C)</strong> At the binding moment depth{" "}
            <M>{String.raw`r\asymp\log m`}</M> (with{" "}
            <M>{String.raw`m=(q-1)/n`}</M>), the over-determined count lane
            coincides, up to an <M>{String.raw`O(1)`}</M> multiplicative factor,
            with the characteristic-<M>{String.raw`p`}</M> moment{" "}
            <M>{String.raw`E_r(\mu_n)=\sum_b|S_b|^{2r}/q`}</M>: the
            count-to-moment ratio satisfies{" "}
            <M>{String.raw`(\mathrm{mult})^{1/2r}\approx1.2`}</M> at{" "}
            <M>{String.raw`n=8,16,32`}</M> across every tested prime, so the
            window threshold is determined by the same object as{" "}
            <M>{String.raw`M(n)`}</M>.
          </p>
        </Theorem>
        <p>
          The consequence is a clean dichotomy. Below and at the window boundary,
          the threshold is the <M>{String.raw`p`}</M>-independent combinatorial
          crossing above. Strictly inside the window, the binding witness size
          descends into the moment regime, where the count equals the
          characteristic-<M>{String.raw`p`}</M> moment, which is controlled by{" "}
          <M>{String.raw`M(n)`}</M>, the BGK wall. The decoupling is a
          genuine structural reduction of the floor question and genuinely not a
          resolution of the window. We regard saying this plainly as part of the
          contribution.
        </p>
      </SubSection>
    </Section>
  );
}
