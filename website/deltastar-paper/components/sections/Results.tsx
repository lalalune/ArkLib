import { Section, SubSection } from "../Section";
import { Eli5 } from "../degen/Eli5";
import { StaircaseFigure } from "../figures/StaircaseFigure";
import { Theorem } from "../Theorem";
import { M } from "../Math";
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

const pins: {
  code: string;
  band: string;
  value: string;
  note: string;
  file: string;
}[] = [
  {
    code: String.raw`\mathrm{RS}[\mathbb{F}_5,\mathbb{F}_5^\times,2]`,
    band: String.raw`\varepsilon^*=2/5`,
    value: String.raw`\delta^*=1/4`,
    note: "first exact MCA threshold for any code",
    file: "DeltaStarExactPinF5",
  },
  {
    code: String.raw`\mathrm{RS}[\mathbb{F}_5,\langle 2\rangle,2]`,
    band: String.raw`\text{every }\delta,\ \varepsilon^*`,
    value: String.raw`\text{full }\varepsilon_{\mathrm{mca}}\text{ profile}`,
    note: "first complete error profile of any code",
    file: "MCAExactProfile",
  },
  {
    code: String.raw`\mathrm{RS}[\mathbb{F},D,k],\ k\le n-2`,
    band: String.raw`\varepsilon^*\in[1/q,2/q)`,
    value: String.raw`\delta^*=1/n`,
    note: "first exact threshold for an infinite family",
    file: "MCADeltaStarHighRateFamily",
  },
  {
    code: String.raw`\mathrm{RS}[\mathbb{F}_{17},\langle 2\rangle,4],\ \rho=1/2`,
    band: String.raw`\varepsilon^*\in[2/17,\,7/17)`,
    value: String.raw`\delta^*=1/4`,
    note: "maximal pin at a deployed rate",
    file: "DeltaStarSecondPinF17Maximal",
  },
  {
    code: String.raw`n=16,\ \rho=1/4`,
    band: String.raw`\varepsilon^*\in[j/17,(j{+}1)/17),\ j\le 5`,
    value: String.raw`\delta^*=j/16`,
    note: "first machine-checked threshold curve",
    file: "VVectorN16",
  },
  {
    code: String.raw`\text{any smooth RS},\ 3(j{-}1)+k\le n`,
    band: String.raw`\varepsilon^*\in[j/q,(j{+}1)/q)`,
    value: String.raw`\delta^*=j/n`,
    note: "the granularity-ladder closed form",
    file: "GranularityLadderRS",
  },
  {
    code: String.raw`\text{any smooth RS},\ e\lesssim(n{-}k)/3`,
    band: String.raw`\varepsilon^*=2^{-128}\text{ (literal)}`,
    value: String.raw`\delta^*=e/n`,
    note: "exact at the prize budget, every field up to the band cap",
    file: "StaircaseBandTheorem",
  },
  {
    code: String.raw`\mathrm{evalCode}[2^\mu,1],\ \mu\ge 3`,
    band: String.raw`\text{explicit band}`,
    value: String.raw`\delta^*=1-3/2^{\mu}`,
    note: "beyond Johnson: dimension-ladder rung 2",
    file: "KKH26DimTwoPin",
  },
];

export function Results() {
  return (
    <Section id="results" num="3" title="Results" wide>
      <div className="prose-col" style={{ marginInline: 0 }}>
        <p>
          All results below are axiom-clean Lean theorems on{" "}
          <code className="inline">main</code>. We organize them as: the exact
          pins (&sect;3.1), the universal staircase law (&sect;3.2), the
          dimension ladder (&sect;3.3), the Welch&ndash;Berlekamp pencil
          programme (&sect;3.4), the M&ouml;bius symmetry and the ownership
          unification (&sect;3.5), and the production-regime bracket
          (&sect;3.6).
        </p>
      </div>

      <SubSection num="3.1" title="Exact thresholds: the first pins for any code">
        <Eli5 k="results-pins" />
        <div className="prose-col" style={{ marginInline: 0 }}>
          <p>
            Before this campaign, no exact value of{" "}
            <M>{String.raw`\delta^*`}</M> existed{" "}
            <Scribble type="underline">for any code</Scribble>. The campaign
            produced a family of them, each as a pair of bracket theorems that
            meet.
          </p>
        </div>
        <div className="mt-8 overflow-x-auto">
          <table className="paper-table">
            <thead>
              <tr>
                <th>Code</th>
                <th>Budget band</th>
                <th>Exact value</th>
                <th>Significance</th>
                <th>Lean file</th>
              </tr>
            </thead>
            <tbody>
              {pins.map((p) => (
                <tr key={p.file}>
                  <td className="num">
                    <M>{p.code}</M>
                  </td>
                  <td className="num">
                    <M>{p.band}</M>
                  </td>
                  <td className="num">
                    <M>{p.value}</M>
                  </td>
                  <td>{p.note}</td>
                  <td>
                    <FileLink f={p.file} />
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
          <p
            className="mt-3 text-[0.78rem]"
            style={{ color: "var(--ink-faint)" }}
          >
            Table 1. Exact machine-checked thresholds. Every row is a pair of
            matching bracket theorems, axiom census{" "}
            <code>propext, Classical.choice, Quot.sound</code>, zero{" "}
            <code>sorry</code>.
          </p>
        </div>
        <div className="prose-col mt-8" style={{ marginInline: 0 }}>
          <p>
            The maximal second pin deserves its statement. The exact explosion
            value{" "}
            <M>{String.raw`\varepsilon_{\mathrm{mca}}(C_{8,4},1/4)=7/17`}</M>{" "}
            was first computed exhaustively by probe, then bounded in Lean by
            the far-coset law; the resulting window is formally maximal.
          </p>
          <Theorem
            kind="Theorem"
            name={<Scribble type="box" padding={3}>maximal pin at rate 1/2</Scribble>}
            file="DeltaStarSecondPinF17Maximal.lean"
            decl="mcaDeltaStar_C84_eq_quarter_maximal"
          >
            For{" "}
            <M>{String.raw`C=\mathrm{RS}[\mathbb{F}_{17},\langle 2\rangle,4]`}</M>{" "}
            (smooth, <M>n=8</M>, rate 1/2):{" "}
            <M>{String.raw`\delta^*(C,\varepsilon^*)=1/4`}</M> for every{" "}
            <M>{String.raw`\varepsilon^*\in[2/17,\,7/17)`}</M>, and the band is
            maximal:{" "}
            <M>{String.raw`\varepsilon_{\mathrm{mca}}(C,1/4)=7/17`}</M> exactly.
          </Theorem>
        </div>
      </SubSection>

      <SubSection num="3.2" title="The universal staircase: a three-regime law">
        <Eli5 k="results-staircase" />
        <StaircaseFigure />
        <div className="prose-col" style={{ marginInline: 0 }}>
          <p>
            The exact pins are instances of a structure. Write <M>b</M> for the
            band of radii with <M>{String.raw`\delta n\in[b-1,b)`}</M> and{" "}
            <M>{String.raw`d=n-k+1`}</M> for the distance. The campaign proved
            that <M>{String.raw`\varepsilon_{\mathrm{mca}}\cdot q`}</M>, as a
            function of distance within each band, obeys a single three-regime
            law, and that the regime thresholds{" "}
            <M>{String.raw`3b-2,\ 3b-3,\ 2b-1`}</M> are exactly support-union
            thresholds: where triples (respectively pairs) of error supports can
            or cannot carry a codeword.
          </p>
        </div>
        <div className="mt-8 overflow-x-auto">
          <table className="paper-table">
            <thead>
              <tr>
                <th>Distance regime</th>
                <th>
                  <M>{String.raw`\varepsilon_{\mathrm{mca}}\cdot q`}</M>
                </th>
                <th>Sides</th>
                <th>Lean artifacts</th>
              </tr>
            </thead>
            <tbody>
              <tr>
                <td className="num">
                  <M>{String.raw`d\ge 3b-2`}</M> (deep)
                </td>
                <td className="num">
                  <M>{String.raw`=\,b`}</M>
                </td>
                <td>both</td>
                <td>
                  <FileLink f="UniversalStaircaseCollapse" />,{" "}
                  <FileLink f="UniversalSpikeFloor" />
                </td>
              </tr>
              <tr>
                <td className="num">
                  <M>{String.raw`d=3b-3`}</M> (top strip row)
                </td>
                <td className="num">
                  <M>{String.raw`=\,n/(b{-}1)`}</M>{" "}
                  <span style={{ color: "var(--ink-faint)" }}>
                    for <M>{String.raw`(b{-}1)\mid n`}</M>
                  </span>
                </td>
                <td>both</td>
                <td>
                  <FileLink f="StripSupExactness" />,{" "}
                  <FileLink f="MonomialStripExplosion" />
                </td>
              </tr>
              <tr>
                <td className="num">
                  <M>{String.raw`d=3b-4`}</M>
                </td>
                <td className="num">
                  <M>{String.raw`\ge n/(b{-}1)`}</M>, <M>{String.raw`\le n`}</M>
                </td>
                <td>bracket</td>
                <td>
                  <FileLink f="BoundarySupExactness" />
                </td>
              </tr>
              <tr>
                <td className="num">
                  <M>{String.raw`2b\le d\le 3b-5`}</M> (lower strip)
                </td>
                <td className="num">
                  <M>{String.raw`\ge n/(b{-}1)`}</M>
                </td>
                <td>lower; sup open</td>
                <td>
                  <FileLink f="MonomialStripExplosion" />
                </td>
              </tr>
              <tr>
                <td className="num">
                  <M>{String.raw`b{+}1\le d\le 2b{-}1`}</M> (boundary),{" "}
                  <M>{String.raw`b\mid n`}</M>
                </td>
                <td className="num">
                  <M>{String.raw`\ge n`}</M>
                </td>
                <td>lower</td>
                <td>
                  <FileLink f="CosetCliqueBoundary" />
                </td>
              </tr>
              <tr>
                <td className="num">
                  <M>{String.raw`d=5,\ b=3,\ 3\mid n`}</M>
                </td>
                <td className="num">
                  <M>{String.raw`=\,n`}</M>
                </td>
                <td>both</td>
                <td>
                  <FileLink f="BoundarySupExactness" />
                </td>
              </tr>
              <tr>
                <td className="num">
                  <M>{String.raw`d=5,\ b=3,\ 3\nmid n`}</M>
                </td>
                <td className="num">
                  <M>{String.raw`\le n-1`}</M>; <M>{String.raw`=\,n-1`}</M> at{" "}
                  <M>n=8</M>
                </td>
                <td>
                  both at <M>n=8</M>
                </td>
                <td>
                  <FileLink f="BoundaryDefectBound" />
                </td>
              </tr>
            </tbody>
          </table>
          <p
            className="mt-3 text-[0.78rem]"
            style={{ color: "var(--ink-faint)" }}
          >
            Table 2. The three-regime staircase law, per band <M>b</M>. The
            production domain <M>{String.raw`n=2^{\mu}`}</M> has{" "}
            <M>{String.raw`3\nmid n`}</M> and <M>{String.raw`b\mid n`}</M> at
            every 2-power band: boundary rows recur at every halving of the
            distance budget, and strip explosions fire at every band.
          </p>
        </div>
        <div className="prose-col mt-8" style={{ marginInline: 0 }}>
          <p>
            The deep regime gives the closed form on the granularity bands, and,
            crucially, the law survives contact with the literal prize budget:
          </p>
          <Theorem
            kind="Theorem"
            name={
              <Scribble type="box" padding={3} tone="verified">
                staircase at the literal budget
              </Scribble>
            }
            file="StaircaseBandTheorem.lean"
            decl="mcaDeltaStar_staircase_band"
          >
            For <M>{String.raw`1\le e`}</M>,{" "}
            <M>{String.raw`3(e-1)+k\le n`}</M>, and{" "}
            <M>{String.raw`e\cdot 2^{128}\le q<(e+1)\cdot 2^{128}`}</M>:{" "}
            <M>{String.raw`\delta^*(\mathrm{RS},2^{-128})=e/n`}</M> exactly. At
            production shape (<M>{String.raw`n=2^{25}`}</M>,{" "}
            <M>{String.raw`k=2^{24}`}</M>) this covers every rung{" "}
            <M>{String.raw`1\le e\le 5{,}592{,}406`}</M>, i.e. every field size
            up to <M>{String.raw`\approx 2^{150.4}`}</M>.
          </Theorem>
          <p>
            The law&rsquo;s reach honestly caps at{" "}
            <M>{String.raw`q\lesssim ((n-k)/3)\cdot 2^{128}`}</M>. The
            production-core parameterization{" "}
            <M>{String.raw`q\ge n^2\cdot 2^{128}`}</M>, where the staircase
            climbs through the open window, is untouched by it; that is &sect;5.
          </p>
        </div>
      </SubSection>

      <SubSection
        num="3.3"
        title="The dimension ladder: unconditional pins beyond Johnson"
      >
        <div className="prose-col" style={{ marginInline: 0 }}>
          <p>
            At fixed code dimension, an ownership-counting device pins{" "}
            <M>{String.raw`\delta^*`}</M> exactly, strictly inside the open
            window, beyond the Johnson radius, with no conditional hypothesis.
            The rung-1 pin (<FileLink f="KKH26DimOnePin" />) was the first
            unconditional in-window exact value; rung 2 climbs:
          </p>
          <Theorem
            kind="Theorem"
            name="dimension ladder, rung 2"
            file="KKH26DimTwoPin.lean"
            decl="kkh26_dimTwo_deltaStar_pin"
          >
            For the dimension-two code on the smooth domain (affine words, rate{" "}
            <M>{String.raw`2/2^{\mu}`}</M>), every <M>{String.raw`\mu\ge 3`}</M>{" "}
            and every <M>{String.raw`\varepsilon^*`}</M> in an explicit
            nonempty band: <M>{String.raw`\delta^* = 1-3/2^{\mu}`}</M> exactly.
            Concretely: <M>{String.raw`\delta^*=5/8`}</M> at the NTT prime{" "}
            <M>{String.raw`\mathbb{F}_{12289}`}</M>, rate 1/4, strictly between
            Johnson (<M>{String.raw`1/2`}</M>) and capacity (
            <M>{String.raw`3/4`}</M>).
          </Theorem>
          <p>
            The device behind both rungs is the same: a non-degenerate{" "}
            <M>{String.raw`(k{+}1)`}</M>-tuple inside a bad witness{" "}
            <em>determines</em> its scalar, distinct bad scalars own disjoint
            tuple sets, and pigeonhole bounds the bad count. The recorded ladder
            law extends the family to every fixed dimension{" "}
            <M>{String.raw`r\lesssim\sqrt n`}</M> and provably stalls there, a
            calibration family every future candidate{" "}
            <M>{String.raw`\delta^*`}</M> law must reproduce.
          </p>
        </div>
      </SubSection>

      <SubSection num="3.4" title="The Welch–Berlekamp pencil programme">
        <Eli5 k="results-wb" />
        <div className="prose-col" style={{ marginInline: 0 }}>
          <p>
            The campaign&rsquo;s most structural arc reformulates badness as
            linear algebra. A scalar <M>{String.raw`\gamma`}</M> is bad at slack{" "}
            <M>w</M> only if the Welch&ndash;Berlekamp system, linear in a
            locator/numerator pair <M>{String.raw`(\ell,R)`}</M>, is solvable;
            along the line the coefficient matrix is a linear <em>pencil</em>{" "}
            <M>{String.raw`M_0+\gamma M_1`}</M>, and determinant root-counting
            takes over. No decoding theory appears anywhere in the chain.
          </p>
          <Theorem
            kind="Theorem"
            name="WB-1, the pencil bound"
            file="WBPencilBound.lean"
            decl="wbSolvable_line_card_le"
          >
            Below the unique-decoding radius, if the direction{" "}
            <M>{String.raw`u_1`}</M> is not itself WB-solvable at slack{" "}
            <M>w</M>, then at most <M>{String.raw`w+2`}</M> scalars{" "}
            <M>{String.raw`\gamma`}</M> make the line{" "}
            <M>{String.raw`u_0+\gamma u_1`}</M> WB-solvable, for every offset{" "}
            <M>{String.raw`u_0`}</M>.
          </Theorem>
          <Theorem
            kind="Theorem"
            name="WB-2, the rational-pair reduction"
            file="WBPencilRationalReduction.lean"
            decl="epsMCA_le_max_doublyRational"
          >
            At every radius below unique decoding,{" "}
            <M>{String.raw`\varepsilon_{\mathrm{mca}}\le\max\bigl((w{+}3)/q,\ \sup_{\text{doubly rational stacks}}\bigr)`}</M>
            : the MCA adversary provably lives in the thin, fully parameterized
            family of stacks whose rows are rational functions{" "}
            <M>{String.raw`R/\ell`}</M> of bounded degree on the domain.
          </Theorem>
          <p>
            Two further theorems close the easy branches outright: genuinely
            rational pairs below the ladder reach admit <em>zero</em> bad
            scalars (<FileLink f="WBPencilLadderZero" />), and codeword rows
            admit at most one, at <em>every</em> radius and for every linear
            code (<FileLink f="WBPencilPolynomialRow" />). The capstone packages
            the below-UDR law behind a single named hypothesis:
          </p>
          <Theorem
            kind="Theorem"
            name="the below-UDR law"
            file="WBPencilBelowUDR.lean"
            decl="epsMCA_le_below_udr"
            conditional="WindowRationalBounded"
          >
            Modulo exactly one named Prop,{" "}
            <code className="inline">WindowRationalBounded</code> (doubly
            WB-solvable stacks have at most <M>{String.raw`w+3`}</M> bad
            scalars; proven below the ladder reach, probe-supported in the
            window at two scales):{" "}
            <M>{String.raw`\varepsilon_{\mathrm{mca}}(\mathrm{RS},\delta)\le (w{+}3)/q`}</M>{" "}
            at every radius below unique decoding, and at{" "}
            <M>{String.raw`\varepsilon^*=2^{-128}`}</M> the unconditional
            production floor moves from{" "}
            <M>{String.raw`\approx(1-\rho)/3`}</M> to the unique-decoding radius{" "}
            <M>{String.raw`(1-\rho)/2`}</M>.
          </Theorem>
          <p>
            The adversary the residual Prop must tame was <em>found</em>, not
            conjectured: adversarial probing located rational pairs attaining{" "}
            <M>{String.raw`w+1`}</M> bad scalars in the window, and the extremal
            stacks are invariant under the M&ouml;bius involution{" "}
            <M>{String.raw`x\mapsto -1/x`}</M>, replicated at two scales, with
            the invariant family dominating general pairs three to one.
          </p>
        </div>
      </SubSection>

      <SubSection
        num="3.5"
        title="Möbius equivariance and the ownership unification"
      >
        <Eli5 k="results-ownership" />
        <div className="prose-col" style={{ marginInline: 0 }}>
          <p>
            That observed symmetry was then proven to be structural. The smooth
            domain is inversion-stable, and a weighted twist repairs the
            non-polynomial inversion:
          </p>
          <Theorem
            kind="Theorem"
            name="Möbius inversion equivariance"
            file="MCAMobiusInversion.lean"
            decl="mcaEvent_rs_inversion"
          >
            On an inversion-stable domain avoiding 0, the twisted action{" "}
            <M>{String.raw`(Tu)(i)=\mathrm{dom}(i)^{k-1}\,u(\sigma i)`}</M> with{" "}
            <M>{String.raw`\sigma\colon x\mapsto -1/x`}</M> preserves the MCA
            event at every scalar. Together with rotation equivariance, the
            full M&ouml;bius group <M>{String.raw`\mathrm{PGL}_2`}</M> acts on
            smooth-domain MCA; for odd <M>k</M> the twist is a genuine
            involution, and T-fixed codewords are exactly the
            reversal-palindromes.
          </Theorem>
          <p>
            The two lanes of the campaign, the WB pencil (below UDR) and the
            dimension ladder (deep interior), then converged on one theorem
            family that contains both as instances:
          </p>
          <Theorem
            kind="Theorem"
            name="the ownership bound"
            file="OwnershipBound.lean"
            decl="badScalars_card_mul_le_ownership"
          >
            Radius-free: a <M>{String.raw`(k{+}1)`}</M>-tuple with nonvanishing
            direction residual inside a bad witness determines its scalar;
            ownership is disjoint across scalars; hence{" "}
            <M>{String.raw`\#\mathrm{bad}\cdot M\le\#\text{tuples}`}</M>{" "}
            whenever every bad scalar owns at least <M>M</M> tuples.
          </Theorem>
          <p>
            Instantiating the ownership engine closed the entire <M>k=1</M>{" "}
            window unconditionally, by direction class:
          </p>
          <ul className="list-disc pl-6 space-y-2">
            <li>
              <em>Polynomial directions</em>: zero bad scalars, every radius (
              <FileLink f="WBPencilPolynomialRow" />).
            </li>
            <li>
              <em>Genuine rational directions</em>: the multiplicity theorem{" "}
              <M>{String.raw`\#\mathrm{bad}\cdot\bigl((n-w)(n-w-\mu)\bigr)\le n^2`}</M>
              , the first unconditional window-valid bound (
              <FileLink f="OwnershipMultiplicity" />); it <em>explains</em> the
              measured window cap rather than merely matching it.
            </li>
            <li>
              <em>Sparse directions</em> (support <M>{String.raw`\le e`}</M>):{" "}
              <M>{String.raw`\#\mathrm{bad}\cdot(n-w-e)\le n\,e`}</M> by a
              popularity argument (<FileLink f="SparseDirectionWindow" />).
              This class is where the window difficulty provably concentrates.
            </li>
          </ul>
          <p className="mt-4">
            The general-<M>k</M> assembly is in progress along a fully specified
            route; its packing piece,{" "}
            <M>{String.raw`\#\mathrm{popular}\cdot(m{+}1{-}k)^k\le n^k`}</M>, is
            proven (<FileLink f="PopularCodewords" />).
          </p>
        </div>
      </SubSection>

      <SubSection num="3.6" title="The production-regime bracket">
        <div className="prose-col" style={{ marginInline: 0 }}>
          <p>
            What does all of this say about the prize parameters themselves? The
            honest assembled state:
          </p>
          <Theorem
            kind="Theorem"
            name="unconditional production floor"
            file="MCADeltaStarProductionFloor.lean"
            decl="mcaDeltaStar_rs_ge_at_secpar"
          >
            At <M>{String.raw`\varepsilon^*=2^{-128}`}</M>, for every smooth RS
            instance at production shape:{" "}
            <M>{String.raw`\delta^*\ \ge\ (\lfloor (n-k)/3\rfloor+1)/n\ \approx\ (1-\rho)/3`}</M>
            , unconditionally.
          </Theorem>
          <p>
            Above the floor, the Johnson lane (the BCIKS20 &sect;5 discharge
            chain, driven through two machine-checked course corrections of the
            paper&rsquo;s own recursion, &sect;4) is reduced to a single named
            residual, <code className="inline">CellPackageSupply</code>, with
            the numeric budget proven: at{" "}
            <M>{String.raw`\varepsilon^*=2^{-128}`}</M>,{" "}
            <M>{String.raw`n\le 2^{30}`}</M>, every{" "}
            <M>{String.raw`q\ge 2^{192}`}</M> puts the whole Johnson range below{" "}
            <M>{String.raw`\delta^*`}</M> modulo that one object (
            <FileLink f="ProductionJohnsonBudget" />). And on the bad side,
            every lower-bound family ever landed, spike, sunflower, pencil,
            triangle, widened pin, is <M>{String.raw`O(n)/q`}</M>: provably
            silent at the prize budget. Certifying any bad radius below 1 at
            production scale needs a single stack with more than{" "}
            <M>{String.raw`q\cdot 2^{-128}\approx 2^{64+}`}</M> bad scalars; no
            known construction comes within polynomial range.
          </p>
        </div>
      </SubSection>
    </Section>
  );
}
