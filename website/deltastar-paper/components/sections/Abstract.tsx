import { M } from "../Math";
import { Scribble } from "../Scribble";

export function Abstract() {
  return (
    <section id="abstract" className="prose-col mt-10">
      <h2 className="sc-label text-[0.95rem] font-semibold mb-4">Abstract</h2>
      <div className="text-[0.99rem]" style={{ color: "var(--ink-secondary)" }}>
        <p>
          Most of mathematics does not need a genius. It needs search, and
          search is{" "}
          <Scribble type="underline">a function of compute</Scribble>. This campaign is an existence proof:
          a fleet of LLM agents, grinding in the open ArkLib repository with the
          Lean&nbsp;4 kernel as the sole arbiter of truth, formalized the entire
          known frontier of a problem that has resisted humans for twenty-five
          years, produced the first exact MCA thresholds ever computed for{" "}
          <em>any</em> code, and refuted twenty-eight attack hypotheses, each
          refutation itself a machine-checked theorem. No reviewer trust, no
          grant cycles, no decades. Hypothesis, probe, proof, kernel. At scale.
        </p>
        <p>
          The target is chosen deliberately. There is no better problem in
          applied mathematics today than fully proving the zkEVM. The threshold{" "}
          <M>{String.raw`\delta^*(C,\varepsilon^*)`}</M> studied here, subject
          of the Ethereum Foundation&rsquo;s{" "}
          <Scribble type="circle" delay={300}>$1M</Scribble> Proximity Prize,
          governs the
          soundness of the FRI- and WHIR-style proximity tests at the heart of
          every modern SNARK. Today these systems run on conservative
          provable bounds; pinning <M>{String.raw`\delta^*`}</M> at the
          conjectured edge would cut verifier queries by an estimated{" "}
          <M>{String.raw`8\times`}</M>, compounding through every proof
          Ethereum verifies. Cheaper proofs, faster finality, a lighter chain.
          The result general enough to be coding theory, useful enough to be
          infrastructure.
        </p>
        <p>
          We report the campaign&rsquo;s results: the first exact thresholds{" "}
          (<M>{String.raw`\delta^*(\mathrm{RS}[\mathbb{F}_5,\mathbb{F}_5^\times,2],\,2/5)=1/4`}</M>{" "}
          and a maximal pin at deployed rate); a universal staircase law proven
          at the literal prize budget{" "}
          <M>{String.raw`\varepsilon^*=2^{-128}`}</M>; unconditional
          beyond-Johnson pins on a dimension ladder; and the Welch&ndash;Berlekamp
          pencil programme reducing the below-unique-decoding regime to a single
          named hypothesis. Every theorem is{" "}
          <Scribble type="underline" tone="verified">axiom-clean</Scribble>,
          zero <code className="inline">sorry</code>. The prize window at
          production rate{" "}
          <Scribble type="highlight" tone="soft" delay={300}>
            remains open
          </Scribble>
          , and we state its four faces precisely, because the method only
          works if the ledger is honest.
        </p>
        <p>
          The implication scales beyond this problem. Verification was the
          bottleneck; the kernel removed it. A swarm of a thousand agents under
          one motivated researcher is a research institution that never sleeps.
          Given enough compute, Vitalik and a swarm could plausibly finish
          Ethereum&rsquo;s remaining roadmap in months, not decades. The unknown
          sciences are not waiting for permission. They are waiting for FLOPs.
        </p>
      </div>
      <div
        className="mt-10 h-px w-full"
        style={{ background: "var(--rule)" }}
      />
    </section>
  );
}
