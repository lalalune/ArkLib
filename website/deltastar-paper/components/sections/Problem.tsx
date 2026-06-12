import { Section, SubSection } from "../Section";
import { Eli5 } from "../degen/Eli5";
import { WindowFigure } from "../figures/WindowFigure";
import { Theorem } from "../Theorem";
import { M, MD } from "../Math";
import { Cite } from "../Cite";
import { Scribble } from "../Scribble";

export function Problem() {
  return (
    <Section id="problem" num="1" title="The problem">
      <p>
        Fix a Reed&ndash;Solomon code{" "}
        <M>{String.raw`C = \mathrm{RS}[\mathbb{F}_q, L, k]`}</M> whose evaluation
        domain <M>L</M> is a <em>smooth</em> multiplicative subgroup of size{" "}
        <M>{String.raw`n = 2^{\mu}`}</M>, at rate{" "}
        <M>{String.raw`\rho = k/n \in \{1/2, 1/4, 1/8, 1/16\}`}</M>, with{" "}
        <M>{String.raw`|\mathbb{F}| < 2^{256}`}</M> and security budget{" "}
        <M>{String.raw`\varepsilon^* = 2^{-128}`}</M>. These are the codes that
        FRI and WHIR actually deploy.
      </p>
      <p>
        The <em>mutual correlated agreement</em> error{" "}
        <M>{String.raw`\varepsilon_{\mathrm{mca}}(C,\delta)`}</M>
        <Cite id="ABF26" /> is a supremum over stacks of words{" "}
        <M>{String.raw`(u_0,u_1)`}</M> of the fraction of <em>bad</em> points on
        the line <M>{String.raw`u_0+\gamma u_1`}</M>: a scalar{" "}
        <M>{String.raw`\gamma`}</M> is bad when the combined word agrees with a
        codeword on a large witness set that admits no joint explanation of both
        rows. It sits at the top of the error hierarchy{" "}
        <M>{String.raw`\varepsilon_{\mathrm{pg}} \le \varepsilon_{\mathrm{ca}} \le \varepsilon_{\mathrm{mca}}`}</M>,
        and it is the quantity that WHIR/FRI-style soundness proofs actually
        consume. The threshold is
      </p>
      <MD>{String.raw`\delta^*(C,\varepsilon^*) \;=\; \sup\{\delta : \varepsilon_{\mathrm{mca}}(C,\delta) \le \varepsilon^*\}.`}</MD>
      <p>
        <em>Pinning</em> <M>{String.raw`\delta^*`}</M> means producing matching
        brackets: a machine-checked proof that{" "}
        <M>{String.raw`\varepsilon_{\mathrm{mca}}(C,\delta^*) \le \varepsilon^*`}</M>{" "}
        and a machine-checked proof that every larger radius fails. In ArkLib the
        definition lives in{" "}
        <code className="inline">Errors.lean</code> and the bracket engine in{" "}
        <code className="inline">MCAThresholdLedger.lean</code>; the good-radius
        set is proven downward closed, so the supremum is genuine.
      </p>

      <WindowFigure />

      <SubSection
        num="1.1"
        title={
          <>
            The window, and why it is{" "}
            <Scribble type="circle" padding={4}>twenty-five years</Scribble>{" "}
            hard
          </>
        }
      >
        <Eli5 k="problem-window" />
        <p>
          Both edges of our knowledge are held by formalized literature. From
          below, full mutual correlated agreement holds up to the Johnson radius{" "}
          <M>{String.raw`1-\sqrt{\rho}`}</M>
          <Cite id="BCIKS20" />
          <Cite id="Hab25" />
          <Cite id="BCHKS25" />. From above, the KKH26 family of explicit bad
          lines forces{" "}
          <M>{String.raw`\delta^* \le 1-\rho-\Theta_{\rho}(1/\log n)`}</M>
          <Cite id="KKH26" />, and the once-hoped &ldquo;up to capacity&rdquo;
          conjectures are simply false: three independent groups refuted them in
          late 2025
          <Cite id="CS25" />
          <Cite id="DG25" />, and the refutations are formalized in-tree. So
        </p>
        <MD>{String.raw`\delta^* \;\in\; \bigl(\,1-\sqrt{\rho}\,,\; 1-\rho-\Theta_{\rho}(1/\log n)\,\bigr),`}</MD>
        <p>
          and the entire problem is to pin it inside that open interval. The
          difficulty has an honest measure: the barrier results of BCHKS25 and
          CS25 couple any upper-bound progress past Johnson to{" "}
          <em>beyond-Johnson list decoding of explicit RS codes</em>, a problem
          that has stood open since Guruswami&ndash;Sudan
          <Cite id="GS99" />. Capacity-achieving list decoding is known for
          random punctured RS
          <Cite id="GZ23" /> and for explicit <em>folded</em> RS
          <Cite id="CZ25" />, but every such proof consumes domain randomness,
          folding side-information, or subspace-design structure that the plain
          smooth domain, a single fixed orbit with zero entropy, does not have.
        </p>
        <p>
          One structural observation makes the problem finite in an exact sense:{" "}
          <M>{String.raw`\varepsilon_{\mathrm{mca}}`}</M> sees the radius only
          through the agreement floor{" "}
          <M>{String.raw`\lceil (1-\delta)n\rceil`}</M>, so it is a step function
          of <M>{String.raw`\delta`}</M> and{" "}
          <M>{String.raw`\delta^*(\varepsilon^*)`}</M> is its generalized
          inverse. The window question is literally: <em>where are the jumps of
          the staircase between Johnson and capacity, and what are the step
          heights?</em>
        </p>
      </SubSection>

      <SubSection num="1.2" title="What was known before the campaign">
        <p>
          No exact value of{" "}
          <M>{String.raw`\delta^*`}</M>, or of{" "}
          <M>{String.raw`\varepsilon_{\mathrm{mca}}`}</M> at any radius, had ever
          been computed for any code. The literature provided the two window
          edges, the at-capacity refutations, and the coupling barrier, all
          asymptotic statements. The campaign began by formalizing all of it:
          seventeen papers wired into the tree as named theorems and named
          hypotheses, so that every later claim would compose against the genuine
          published frontier rather than a paraphrase of it.
        </p>
        <Theorem
          kind="Theorem"
          name="capacity edge, unconditional"
          file="KKH26DeltaStarReduction.lean"
          decl="kkh26_mcaDeltaStar_le"
        >
          For the explicit smooth evaluation codes,{" "}
          <M>{String.raw`\delta^* \le 1 - r/2^{\mu}`}</M>: the near-capacity
          strip is excluded by an explicit family of bad lines.
        </Theorem>
      </SubSection>
    </Section>
  );
}
