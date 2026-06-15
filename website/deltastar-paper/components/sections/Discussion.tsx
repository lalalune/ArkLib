import { Section } from "../Section";
import { M } from "../Math";

export function Discussion() {
  return (
    <Section id="discussion" num="6" title="Discussion: what a kernel contract buys">
      <p>
        The substance of this report is not any single theorem but the shape of
        the ledger. The relevant methodological claim is narrow and, we think,
        defensible: when the publication layer of a mathematical effort is a
        proof checker rather than a human referee, the boundary between what is
        established and what is merely believed becomes third-partyly checkable,
        and the failure modes usually associated with machine-generated
        mathematics are confined to the search layer, where they are harmless.
      </p>
      <p>
        Concretely, the campaign behind this page left, over the
        smooth-domain MCA threshold <M>{String.raw`\delta^*`}</M>: the first
        exact thresholds for explicit small codes (Section&nbsp;3.2); a
        granularity law with its regime boundaries identified and proven
        (Section&nbsp;3.3); an unconditional dimension-ladder ceiling strictly
        inside the beyond-Johnson region; two machine-checked corrections to the
        proof chain it builds on (Section&nbsp;4.3); and the central reduction,
        the <M>{String.raw`\delta^*`}</M> decoupling, which isolates the
        field-dependent part of the floor question onto a single combinatorial
        crossing with no character-sum input (Section&nbsp;5). We are explicit
        that the floor itself is not resolved.
      </p>
      <p>
        The standard objection to language-model mathematics is that such models
        confabulate, and the objection is correct. The answer here is
        architectural, not behavioral: no statement is admitted as proven unless
        the Lean&nbsp;4 kernel accepts it and its axiom census lies within the
        standard foundational budget. The search process produced many wrong
        candidates; twenty-eight refuted hypotheses and a public log of
        retracted overclaims record them. None survives into the labelled-proven
        results, because the medium those results live in does not hold a
        falsehood. Confabulation at the search layer is harmless when the
        publication layer is a proof checker.
      </p>
      <p>
        Under that contract, a refuted hypothesis costs roughly as much as a
        proven theorem and is worth nearly as much, because it permanently
        narrows the search space and is itself recorded as a constraint lemma.
        The disproof log is as load-bearing as the theorem files; the
        self-correction we report in Section&nbsp;6 of the paper (a retracted
        energy bound, caught by an exact probe) is the kind of error the
        contract exists to catch, and did.
      </p>
      <p>
        We are equally explicit about the limit. The residual difficulty
        (Problem&nbsp;CORE) is a recognized character-sum wall, open for roughly
        two decades, and the impossibility results of the paper prove that every
        second-order method (energy, Parseval, spectral) and every
        thickness-monotone method cannot reach it. Nothing in this methodology
        guarantees the wall falls to more compute. What it changes is the cost
        structure around the wall: everything provable short of it is proven, its
        exact shape is formalized, and the problem is left in a state where a
        single new idea has a prepared place to land. That is what we mean by
        mapping the unknown honestly, and we regard it as the durable
        contribution: a famous open problem can be delimited precisely without
        being inflated, because the kernel does not grade on a curve.
      </p>
      <p
        className="mt-10 text-[0.9rem]"
        style={{ color: "var(--ink-faint)" }}
      >
        Everything labelled proven on this page is reproducible from{" "}
        <a href="https://github.com/lalalune/ArkLib">lalalune/ArkLib</a>: clone,
        build, and run <code className="inline">#print axioms</code> on any
        theorem named above. The campaign record is public on ArkLib, consolidated
        in issue #444.
      </p>
    </Section>
  );
}
