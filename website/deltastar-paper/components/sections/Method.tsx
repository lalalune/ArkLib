import { Section, SubSection } from "../Section";
import { Lede } from "../Lede";
import { Eli5 } from "../degen/Eli5";
import { SwarmFigure } from "../figures/SwarmFigure";
import { M } from "../Math";

export function Method() {
  return (
    <Section id="method" num="2" title="Method: an agent fleet under a kernel-enforced honesty contract">
      <Lede>
        Then the swarm arrived. Not one prover but a fleet of them, working in
        public, around the clock, each claim submitted to a referee that
        cannot be argued with, flattered, or fooled. The agents are allowed to
        be wrong as often as they like; the kernel is never wrong about
        whether they are.
      </Lede>
      <p>
        The campaign is a sequence of GitHub issues (#232 &rarr; #334 &rarr; #357
        &rarr; #371) on the open ArkLib repository, each fully distilled into the
        tree before its successor opens. The workers are LLM agents; the referee
        is the Lean&nbsp;4 kernel. The contract has three clauses.
      </p>

      <SwarmFigure />

      <SubSection num="2.1" title="The honesty contract">
        <Eli5 k="method-honesty" />
        <p>
          <strong>Every positive claim is an axiom-clean Lean theorem.</strong>{" "}
          &ldquo;Axiom-clean&rdquo; means{" "}
          <code className="inline">#print axioms</code> reports exactly{" "}
          <code className="inline">propext, Classical.choice, Quot.sound</code>,
          the three axioms of ordinary classical mathematics in Lean, and the
          proof contains zero <code className="inline">sorry</code>. There is no
          appeal to authority, reputation, or plausibility: a claim either
          type-checks or it does not exist.
        </p>
        <p>
          <strong>Every refutation is also a theorem.</strong> When an attack
          hypothesis dies, it is reduced to a sorry-free <em>constraint
          lemma</em> and recorded in a standing disproof log, so the fleet cannot
          re-propose a dead idea and future readers inherit the precise reason it
          failed, as mathematics rather than folklore.
        </p>
        <p>
          <strong>Open problems stay named.</strong> Anything unproven that a
          theorem depends on must be a named <code className="inline">Prop</code>{" "}
          in the tree, never an implicit assumption. Conditional results are
          stated as conditional; the residual surface is enumerable by{" "}
          <code className="inline">grep</code>. Fabricating a closure of the open
          core is structurally impossible: the kernel would reject it.
        </p>
      </SubSection>

      <SubSection num="2.2" title="Hypothesis-slate discipline">
        <p>
          Work proceeds in rounds. Each round opens with a grounding essay and a
          slate of ranked hypotheses, typically nine, spanning reasonable,
          novel, and synthetic attacks. Each hypothesis runs the same gauntlet:
          state the constraints; ask why nobody has done this; check the
          literature for the larp; design a falsification probe; only then
          formalize. Survivors get red-teamed by separate agents whose explicit
          job is to kill them. The campaign disposed of twenty-eight hypotheses
          this way (&sect;4); the survivors are the results of &sect;3.
        </p>
      </SubSection>

      <SubSection num="2.3" title="Probe-then-formalize">
        <Eli5 k="method-probe" />
        <p>
          Before any Lean is written, hypotheses face exact arithmetic.
          Dozens of pre-registered probes (
          <code className="inline">scripts/probes/</code>) compute{" "}
          <M>{String.raw`\varepsilon_{\mathrm{mca}}`}</M> exactly at toy scale
          via a syndrome reduction that collapses the stack space to{" "}
          <M>{String.raw`q^{2(n-k)}`}</M> syndrome pairs, itself later proven
          correct in Lean. Probes are cross-validated at three or more primes
          plus a characteristic-zero anchor; sampling artifacts are documented
          kills. The discipline runs in both directions: probes found the
          countermodels that killed three successive extremality conjectures, and
          probes confirmed predictions (a pencil bound predicting{" "}
          <M>{String.raw`\le 8`}</M> bad scalars where exhaustive computation
          found exactly 7) before formalization was attempted.
        </p>
        <p>
          The pipeline scales to proofs no human would write: one converse branch
          of the census classification is a 1,571-line Lean proof{" "}
          <em>machine-generated</em> from the exact integer certificates of a
          10,395-case probe sweep, then checked by the kernel like any other
          theorem. Certificate-to-Lean generation is an industrial method here,
          not a stunt.
        </p>
      </SubSection>

      <SubSection num="2.4" title="Why this is the interesting part">
        <p>
          Nothing in &sect;2.1&ndash;2.3 is specific to coding theory. The
          contract turns a famous open problem into a target for machine-scale
          search in which <em>honesty is not a property of the searcher</em>.
          LLM agents confabulate; fleets of them confabulate at scale. The Lean
          kernel does not care. Every theorem in &sect;3 should be read with
          that in mind: not one of them depends on trusting the agents, the
          authors, or this page. The repository is public; the axiom census is
          reproducible by one command.
        </p>
      </SubSection>
    </Section>
  );
}
