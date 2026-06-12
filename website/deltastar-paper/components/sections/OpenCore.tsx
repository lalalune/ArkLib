import { Section, SubSection } from "../Section";
import { Eli5 } from "../degen/Eli5";
import { M, MD } from "../Math";
import { Cite } from "../Cite";
import { Scribble } from "../Scribble";

const REPO =
  "https://github.com/lalalune/ArkLib/blob/main/ArkLib/Data/CodingTheory/ProximityGap";

function FileLink({ f }: { f: string }) {
  return (
    <a href={`${REPO}/${f}.lean`}>
      <code>{f}</code>
    </a>
  );
}

const faces = [
  {
    n: "i",
    title: "List decoding",
    body: "Beyond-Johnson list decoding of explicit smooth-domain RS: a poly(n) list bound at some radius past the Johnson radius. Open since Guruswami\u2013Sudan; the CS25/BCHKS25 coupling makes this the canonical hard face.",
    anchor: "RSListDecodingFrontier",
  },
  {
    n: "ii",
    title: "Character sums",
    body: "Per-frequency sub-\u221aq bounds for incomplete character sums over smooth multiplicative subgroups. The campaign pinned the analytic kernel at exactly \u221aq from both sides (Parseval average from below, Gauss-sum completion from above, no Weil input): the open core is beating \u221aq per frequency.",
    anchor: "SubgroupGaussSumWorstCase",
  },
  {
    n: "iii",
    title: "Bad-side families",
    body: "Constructing a single stack with more than q\u00b72\u207b\u00b9\u00b2\u2078 bad scalars at some radius below 1. Every family ever landed is O(n)/q \u2014 at production scale a winning stack needs roughly 2\u2076\u2074 bad scalars, and no known construction comes within polynomial range.",
    anchor: "KKH26WitnessSpread",
  },
  {
    n: "iv",
    title: "Line\u2013ball incidence",
    body: "New from this campaign: the maximum incidence of an affine line with far-coset direction against the weight-\u230a\u03b4n\u230b syndrome ball. Equivalently, the multiplicity profile of the ratio sequence of two GRS syndromes \u2014 a Littlewood\u2013Offord problem in F_q.",
    anchor: "FarCosetExplosion",
  },
];

export function OpenCore() {
  return (
    <Section id="open-core" num="5" title="The open core, precisely">
      <p>
        We state plainly what is not known. The prize problem, pinning{" "}
        <M>{String.raw`\delta^*`}</M> at production rate inside the window
      </p>
      <MD>{String.raw`\bigl(\,1-\sqrt{\rho}\,,\ 1-\rho-\Theta_{\rho}(1/\log n)\,\bigr)`}</MD>
      <p>
        is{" "}
        <Scribble type="highlight" tone="soft">
          <strong>open</strong>
        </Scribble>
        . After roughly 120 axiom-clean files and 28
        disposed hypotheses, the honest residue is small enough to enumerate.
      </p>

      <SubSection num="5.1" title="The four faces">
        <Eli5 k="opencore-faces" />
        <p>
          The open core has four equivalent faces, inter-reducible through
          proven in-tree reductions; progress on any one moves all four.
        </p>
        <div className="mt-6 space-y-5">
          {faces.map((f) => (
            <div
              key={f.n}
              className="pl-5"
              style={{ borderLeft: "2px solid var(--rule)" }}
            >
              <p className="font-semibold">
                ({f.n}) {f.title}
                <span
                  className="ml-3 font-normal text-[0.8rem]"
                  style={{ color: "var(--ink-faint)" }}
                >
                  anchor: <FileLink f={f.anchor} />
                </span>
              </p>
              <p
                className="mt-1 text-[0.95rem]"
                style={{ color: "var(--ink-secondary)" }}
              >
                {f.body}
              </p>
            </div>
          ))}
        </div>
      </SubSection>

      <SubSection num="5.2" title="The named residuals">
        <p>
          Everything conditional in &sect;3 is conditional on an explicit,
          grep-able object. There are three that matter:
        </p>
        <ul className="list-disc pl-6 space-y-3 mt-4">
          <li>
            <code className="inline">CellPackageSupply</code> (
            <FileLink f="Hab25JohnsonPackageSupply" />) — the BCIKS20 &sect;5
            per-cell heavy-agreement package. The full consumer chain to the
            Johnson discharge is proven; the package itself, whose{" "}
            <code className="inline">hmonic</code> field is the identified
            design tension, is not.
          </li>
          <li>
            <code className="inline">RegimeIIIGoodness</code> (
            <FileLink f="KKH26RegimeSplit" />) — the type-enforced gap between
            the Johnson lane and the pin. A proven weld shows that even a full
            Johnson discharge covers only{" "}
            <M>{String.raw`\delta<1-\sqrt{\rho}-o(1)`}</M>, and that regime III
            is nonempty at every live parameter point: the Johnson lane alone
            never reaches the pin. This honesty is itself a theorem.
          </li>
          <li>
            <code className="inline">WindowRationalBounded</code> (
            <FileLink f="WBPencilBelowUDR" />) — the below-UDR residual:
            doubly WB-solvable stacks carry at most{" "}
            <M>{String.raw`w+3`}</M> bad scalars. Proven below the ladder
            reach, probe-supported in the window at two scales, with the
            extremal (M&ouml;bius-symmetric) adversary explicitly located and
            the <M>k=1</M> case fully closed.
          </li>
        </ul>
      </SubSection>

      <SubSection num="5.3" title="What the wall is, in one sentence">
        <p>
          Via the formalized CS25 coupling
          <Cite id="CS25" />, the window&rsquo;s sup side is equivalent in its
          regime to beyond-Johnson list decoding of explicit smooth-domain RS
          codes; the same wall reached from six independent directions
          (the KKH26 census, the characteristic-zero collision law, pencil
          moments, additive energy, vertical thresholds, divisibility events)
          presents each time as the same quantity: per-frequency cancellation
          past <M>{String.raw`\sqrt q`}</M> on smooth multiplicative subgroup
          character sums. The campaign did not breach it. It measured it,
          formalized its shape, and arranged the architecture so that any future
          breakthrough lands as a single lemma.
        </p>
      </SubSection>
    </Section>
  );
}
