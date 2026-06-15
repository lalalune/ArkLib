import { M } from "../Math";

export function Abstract() {
  return (
    <section id="abstract" className="prose-col mt-10">
      <h2 className="sc-label text-[0.95rem] font-semibold mb-4">Abstract</h2>
      <div className="text-[0.99rem]" style={{ color: "var(--ink-secondary)" }}>
        <p>
          The mutual correlated agreement (MCA) threshold{" "}
          <M>{String.raw`\delta^*`}</M> of a Reed&ndash;Solomon code governs the
          soundness of the proximity tests at the heart of FRI-based interactive
          oracle proofs. Determining <M>{String.raw`\delta^*`}</M> for explicit
          smooth-domain codes, the <M>{String.raw`2`}</M>-power
          multiplicative subgroups required by the FFT, in the
          beyond-Johnson window is a recognized open problem, equivalent to a
          quantitative form of explicit Reed&ndash;Solomon list decoding to
          capacity. We report a formal-verification study of{" "}
          <M>{String.raw`\delta^*`}</M> conducted in Lean&nbsp;4 over the ArkLib
          library. Every result we label <em>proven</em> is a kernel-checked
          theorem with an explicit axiom census; every numerical statement is
          labelled <em>computational</em> and is reproducible by exact
          enumeration; every unresolved statement is labelled an{" "}
          <em>open problem</em> or <em>conjecture</em>.
        </p>
        <p>
          Our principal contribution is a structural reduction we call the{" "}
          <strong>
            <M>{String.raw`\delta^*`}</M> decoupling
          </strong>
          . We prove, machine-checked and uniformly in the field
          characteristic, that the over-determined far-line incidence count is a
          union of per-witness singletons and is therefore bounded by the
          witness count, hence is <M>{String.raw`p`}</M>-independent in the thin
          (prize) regime. We compute its exact closed form{" "}
          <M>{String.raw`I_{\max}(n)=n^3/32-n^2/8+1`}</M> and the exact
          windowed-budget threshold{" "}
          <M>{String.raw`\delta^*=\tfrac12+(\tfrac1{2\rho}-1)/n`}</M>. The
          consequence we wish to state precisely is a clean reduction,{" "}
          <em>not</em> a solution: whether the MCA floor attains its conjectured
          beyond-Johnson value reduces to a single combinatorial question
          (whether the security budget{" "}
          <M>{String.raw`\varepsilon^* q`}</M> crosses the incidence decay curve{" "}
          <M>{String.raw`I(s)`}</M> at witness size{" "}
          <M>{String.raw`s^*-k=\Theta(n/\log n)`}</M>), with no
          character-sum input.
        </p>
        <p>
          We show, also computationally, that the <em>window</em> threshold does{" "}
          <em>not</em> decouple: at the binding moment depth the over-determined
          count coincides with the characteristic-<M>{String.raw`p`}</M> moment,
          so the window threshold remains tied to the
          Bourgain&ndash;Glibichuk&ndash;Konyagin (BGK) square-root-cancellation
          wall. We accompany the decoupling with a family of exact sub-Johnson{" "}
          <M>{String.raw`\delta^*`}</M> pins, unconditional beyond-Johnson
          dimension-ladder ceilings, and several machine-checked impossibility
          results delimiting which methods can and cannot reach the floor. The
          floor-equals-conjectured-value question is stated as the central open
          problem; we do not claim to resolve it.
        </p>
      </div>
      <div className="mt-10 h-px w-full" style={{ background: "var(--rule)" }} />
    </section>
  );
}
