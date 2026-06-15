import { Section } from "../Section";
import { Intuition } from "../Intuition";
import { M, MD } from "../Math";
import { Cite } from "../Cite";
import { WindowFigure } from "../figures/WindowFigure";

export function Problem() {
  return (
    <Section id="problem" num="1" title="The threshold and the window">
      <Intuition>A proximity test lets a verifier check that a committed word is close to a Reed-Solomon codeword by inspecting only a few positions. It stays sound only out to an agreement radius: below the threshold an adversary cannot forge agreement, above it they can. Call that exact threshold delta-star. For the structured (smooth) domains real FFT-based proof systems use, and in the regime past the classical Johnson radius, no one knows delta-star exactly. Pinning it is the problem.</Intuition>
      <p>
        Modern interactive oracle proofs of proximity (FRI
        <Cite id="BCIKS20" /> and its successors STIR and WHIR
        <Cite id="BCHKS25" />) reduce the soundness of a low-degree test
        to a proximity gap for Reed&ndash;Solomon codes. The sharp quantitative
        form of this phenomenon is the mutual correlated agreement (MCA)
        property of Arnon, Boneh, and Fenzi<Cite id="ABF26" />. For a linear
        code <M>{String.raw`C`}</M> and target error{" "}
        <M>{String.raw`\varepsilon^*`}</M> one defines the MCA threshold
      </p>
      <MD>{String.raw`\delta^*(C,\varepsilon^*)=\sup\{\delta:\ \varepsilon_{\mathrm{mca}}(C,\delta)\le\varepsilon^*\}.`}</MD>
      <p>
        It controls the soundness error of the proximity test and hence the
        query complexity, proof size, and verification cost of every system
        built on it. The case relevant to deployed proof systems uses{" "}
        <em>smooth</em> evaluation domains: a multiplicative subgroup{" "}
        <M>{String.raw`\mu_n\subseteq\mathbb{F}_p^\times`}</M> of{" "}
        <M>{String.raw`2`}</M>-power order <M>{String.raw`n=2^\mu`}</M>, on
        which the FFT operates. Determining{" "}
        <M>{String.raw`\delta^*`}</M> for explicit smooth-domain codes above the
        Johnson bound is open; as<Cite id="ABF26" /> record, it is equivalent to
        a quantitative form of beyond-Johnson list decoding of explicit
        Reed&ndash;Solomon codes.
      </p>

      <h3 className="text-[1.13rem] font-semibold mt-10 mb-4">
        The far-line incidence identity
      </h3>
      <p>
        We use the exact identity, formalized in ArkLib, that the MCA error is
        governed by the far-line incidence: for the worst direction,
      </p>
      <MD>{String.raw`q\cdot\varepsilon_{\mathrm{mca}}(C,\delta)=\max_{u_0,u_1}\,\#\{\gamma\in\mathbb{F}:\ \Delta(u_0+\gamma u_1,C)\le\delta\}.`}</MD>
      <p>
        Hence{" "}
        <M>{String.raw`\delta^*=\sup\{\delta:\ \max I(\delta)\le q\varepsilon^*\}`}</M>:
        the threshold is where the worst far-line incidence count crosses the
        security budget <M>{String.raw`q\varepsilon^*`}</M>. The entire study
        below is an analysis of this crossing.
      </p>

      <h3 className="text-[1.13rem] font-semibold mt-10 mb-4">
        The window
      </h3>
      <p>
        Three radii organize the picture. The unique-decoding radius{" "}
        <M>{String.raw`(1-\rho)/2`}</M> and the Johnson radius{" "}
        <M>{String.raw`1-\sqrt\rho`}</M> are classical; below the latter the
        list size is bounded and <M>{String.raw`\delta^*`}</M> is accessible
        (Section&nbsp;4). The <em>window</em> is the interval
      </p>
      <WindowFigure />
      <p>
        between Johnson and the capacity radius{" "}
        <M>{String.raw`1-\rho`}</M>. The capacity radius is provably unattainable
        with polynomial soundness<Cite id="CS25" />, so{" "}
        <M>{String.raw`\delta^*`}</M> is strictly interior. The prize regime
        fixes <M>{String.raw`\varepsilon^*=2^{-128}`}</M> and a thin field{" "}
        <M>{String.raw`q=n^\beta`}</M>, <M>{String.raw`\beta\approx4\text{--}5`}</M>,
        so the budget <M>{String.raw`q\varepsilon^*=2^{-128}n^\beta`}</M> is
        super-linear in <M>{String.raw`n`}</M>.
      </p>

      <h3 className="text-[1.13rem] font-semibold mt-10 mb-4">
        The Gauss-sum object
      </h3>
      <p>
        The far-line incidence in the smooth case is controlled by an incomplete
        character sum. For <M>{String.raw`b\in\mathbb{F}_p`}</M> set{" "}
        <M>{String.raw`S_b=\sum_{x\in\mu_n}e_p(bx)`}</M> and{" "}
        <M>{String.raw`M(n)=\max_{b\not\equiv0}|S_b|`}</M>. Because{" "}
        <M>{String.raw`-1\in\mu_n`}</M> each <M>{String.raw`S_b`}</M> is real.
        The Bourgain&ndash;Glibichuk&ndash;Konyagin (BGK) bound asserts
        square-root cancellation{" "}
        <M>{String.raw`M(n)\le n^{1/2+o(1)}`}</M> for thin subgroups; the best
        explicit exponent in range is <M>{String.raw`n^{0.989}`}</M>, while the
        floor needs <M>{String.raw`n^{1/2+o(1)}`}</M>. We call this the{" "}
        <strong>BGK wall</strong>; it is the analytic obstruction that the
        window threshold remains tied to.
      </p>
    </Section>
  );
}
