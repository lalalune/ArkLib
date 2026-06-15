import { Section, SubSection } from "../Section";
import { Intuition } from "../Intuition";
import { M, MD } from "../Math";
import { Theorem } from "../Theorem";
import { Cite } from "../Cite";

export function Results() {
  return (
    <Section id="results" num="3" title="The δ* decoupling">
      <Intuition>The central finding is a simplification. The relevant count of bad scalars, which a priori could depend on the field size in a subtle analytic way, turns out to be a sum of isolated contributions and therefore does not depend on the field size at all in this regime. This detaches delta-star from the hard analytic obstruction and turns the leftover question into pure combinatorics.</Intuition>
      <p>
        The central structural result is that the <em>over-determined</em>{" "}
        far-line incidence, the count that governs the threshold below and
        at the boundary of the window, is purely combinatorial and
        independent of the field characteristic. We state its three components:{" "}
        <M>{String.raw`p`}</M>-independence, the closed form, and the windowed
        threshold.
      </p>

      <SubSection num="3.1" title="Over-determination and p-independence">
        <p>
          Fix the dimension <M>{String.raw`k`}</M> and a witness size{" "}
          <M>{String.raw`s`}</M>. A <em>witness</em> for a far line at radius{" "}
          <M>{String.raw`\delta=1-s/n`}</M> is a codeword agreeing with{" "}
          <M>{String.raw`u_0+\gamma u_1`}</M> on a set{" "}
          <M>{String.raw`S\subseteq\mu_n`}</M> of size{" "}
          <M>{String.raw`|S|=s`}</M>. The regime{" "}
          <M>{String.raw`s-k\ge2`}</M> is <em>over-determined</em>: a codeword
          of dimension <M>{String.raw`k`}</M> is forced through more than{" "}
          <M>{String.raw`k+1`}</M> points and is therefore pinned.
        </p>

        <Theorem
          name="Over-determined incidence is a union of singletons"
          file="Frontier/OverdetIncidenceUnionCount.lean"
          decl="farIncidence_affine_le_witnesses"
        >
          <p>
            Let <M>{String.raw`F`}</M> be any finite field,{" "}
            <M>{String.raw`V`}</M> an <M>{String.raw`F`}</M>-vector space, and
            let a finite witness family <M>{String.raw`T`}</M> carry, for each{" "}
            <M>{String.raw`S\in T`}</M>, a subspace{" "}
            <M>{String.raw`W_S\le V`}</M> and vectors{" "}
            <M>{String.raw`a_S,b_S\in V`}</M>. If every witness is far,{" "}
            <M>{String.raw`b_S\notin W_S`}</M>, then each per-witness solution
            set <M>{String.raw`\{\gamma: a_S+\gamma b_S\in W_S\}`}</M> is a
            subsingleton, and
          </p>
          <MD>{String.raw`\#\{\gamma\in F:\ \exists\,S\in T,\ a_S+\gamma b_S\in W_S\}\ \le\ \#T.`}</MD>
          <p className="m-0">
            The bound is uniform in <M>{String.raw`F`}</M>: it does not depend on{" "}
            <M>{String.raw`|F|=p`}</M>. Hence the over-determined far-line
            incidence is a <M>{String.raw`p`}</M>-independent combinatorial
            count, bounded by the number of far witnesses.
          </p>
        </Theorem>

        <p>
          This is the source of the decoupling: in the over-determined regime
          the incidence count is determined by the cyclotomic combinatorics of{" "}
          <M>{String.raw`\mu_n`}</M>, not by arithmetic in{" "}
          <M>{String.raw`\mathbb{F}_p`}</M>. The threshold inherited from it is
          therefore computable in characteristic zero, and the open part of the
          problem is isolated to where the over-determined regime ends.
        </p>
      </SubSection>

      <SubSection num="3.2" title="The exact closed form">
        <Theorem
          name="Closed form of the over-determined incidence maximum"
          file="OverdetIncidenceMaxClosedForm.lean"
          decl="overdetIncidenceMax_values, overdetIncidenceMax_gt_budget"
        >
          <p>
            Set <M>{String.raw`I_{\max}(n)=n^3/32-n^2/8+1`}</M>, equivalently{" "}
            <M>{String.raw`2m^3-2m^2+1`}</M> with{" "}
            <M>{String.raw`n=4m`}</M>. Then:
          </p>
          <p className="m-0">
            <strong>(P)</strong> the arithmetic identity{" "}
            <M>{String.raw`2m^3-2m^2=2m^2(m-1)`}</M> and the budget-domination{" "}
            <M>{String.raw`I_{\max}(n)>n`}</M> for{" "}
            <M>{String.raw`m\ge2`}</M> hold as kernel-checked theorems over{" "}
            <M>{String.raw`\mathbb{N}`}</M>;{" "}
            <strong>(C)</strong>{" "}
            <M>{String.raw`I_{\max}(n)`}</M> equals the exact over-determined
            incidence maximum, attained at the antipodal direction{" "}
            <M>{String.raw`(n/2,\,n/2-1)`}</M>, verified by full-direction search
            and exact integer cross-check for{" "}
            <M>{String.raw`n=8,12,\dots,40`}</M> (the sequence{" "}
            <M>{String.raw`9,37,97,201,361,589,897,1297,1801`}</M>).
          </p>
        </Theorem>
        <p>
          The kernel certifies the cubic&rsquo;s arithmetic and its strict
          domination over the linear budget <M>{String.raw`n=4m`}</M>; the
          identification of the cubic with the measured incidence is established
          computationally (exact enumeration, not sampling) on the stated range.
          We keep the two apart deliberately.
        </p>
      </SubSection>

      <SubSection num="3.3" title="The windowed-budget threshold">
        <p>
          The over-determined incidence <M>{String.raw`I(s)`}</M> decays from a
          cubic <M>{String.raw`\sim n^3`}</M> at{" "}
          <M>{String.raw`s=k+2`}</M> to a constant plateau{" "}
          <M>{String.raw`\sim 2k+1`}</M> near <M>{String.raw`s\sim n/2`}</M>.
          With the windowed budget <M>{String.raw`B=n`}</M>, the threshold is
          exact.
        </p>
        <Theorem
          kind="Proposition"
          name="Windowed-budget threshold"
          file="OverdetIncidenceMaxClosedForm.lean"
          decl="rust-pg engine, computational"
          conditional="exact computation, n ≤ 24"
        >
          <p className="m-0">
            <strong>(C)</strong> For the over-determined monomial far-line
            incidence with windowed budget <M>{String.raw`B=n`}</M>,{" "}
            <M>{String.raw`\delta^*=\tfrac12+(\tfrac1{2\rho}-1)/n`}</M> and{" "}
            <M>{String.raw`s^*=n/2-\tfrac1{2\rho}+1`}</M>, verified exactly for{" "}
            <M>{String.raw`\rho=1/4`}</M> and <M>{String.raw`\rho=1/8`}</M> and
            validated against the canonical pin{" "}
            <M>{String.raw`\delta^*(\mu_{16},k=4)=9/16`}</M> by an independent
            exact engine.
          </p>
        </Theorem>
        <p>
          With the literal windowed budget <M>{String.raw`B=n`}</M> this gives{" "}
          <M>{String.raw`\delta^*\to\tfrac12`}</M> as{" "}
          <M>{String.raw`n\to\infty`}</M> for every rate, the{" "}
          <M>{String.raw`1/2`}</M>-agreement (Plotkin-type) threshold, which is{" "}
          <em>below</em> the conjectured floor{" "}
          <M>{String.raw`1-\rho-\Theta(1/\log n)`}</M>. The conjectured floor
          corresponds to a different, super-linear budget. The budget
          normalization is everything; this is the subject of the next section.
        </p>
      </SubSection>
    </Section>
  );
}
