import { Section } from "../Section";
import { Lede } from "../Lede";
import { M } from "../Math";
import { Scribble } from "../Scribble";

export function Discussion() {
  return (
    <Section id="discussion" num="6" title="Discussion: kernel-checked grind is unfakeable">
      <Lede>
        What does it mean that any of this worked? Not that machines replaced
        mathematicians, but that verification stopped being the bottleneck,
        and the moment it did, mathematical progress started behaving like a
        function of compute. That is the part that generalizes.
      </Lede>
      <p>
        The headline of this report is not any single theorem. It is the shape
        of the ledger. In a matter of weeks, an agent fleet took a problem on
        which the published frontier had not produced one exact value in
        twenty-five years and left behind: the first exact thresholds for any
        code, a universal structural law with its regime boundaries identified
        and proven, an infinite calibration family of in-window pins, a complete
        unconditional classification of the <M>k=1</M> window, two corrections
        to the literature&rsquo;s own proof chain, and a map of the open core
        sharp enough that the remaining mathematics fits in three named
        Props.
      </p>
      <p>
        The standard objection to LLM mathematics is that language models
        confabulate, and the objection is correct. The campaign&rsquo;s answer
        is architectural, not behavioral: no claim exists unless the Lean
        kernel accepts it, and the axiom census of every theorem is one command
        away. The agents tried wrong things constantly; twenty-eight refuted
        hypotheses and a public log of retracted overclaims say so. None of
        that survives into the results, because the medium the results live in{" "}
        <Scribble type="underline">cannot hold a falsehood</Scribble>. Confabulation at the search layer is
        harmless, even useful, when the publication layer is a proof checker.
      </p>
      <p>
        Under that contract, progress becomes a function of compute in a
        concrete sense. Hypothesis generation, probe design, formalization,
        and red-teaming all parallelize across agents; the kernel serializes
        nothing but truth. The interesting economics: a refuted hypothesis
        costs roughly as much as a proven theorem and is worth nearly as much,
        because it permanently shrinks the search space for every subsequent
        agent. Mathematical knowledge here compounds the way a codebase does,
        and the disproof log is as load-bearing as the theorem files.
      </p>
      <p>
        We are explicit about the limit case. The wall of &sect;5.3 is a
        genuine mathematical barrier; nothing about this method guarantees it
        falls to more compute, and the campaign&rsquo;s own no-go lemmas prove
        that several natural compute-shaped attacks cannot work. What the
        method changes is the cost structure around the wall: everything
        provable short of it gets proven, the wall&rsquo;s exact shape gets
        formalized, and the problem is left in a state where a single new idea,
        human or machine, has a prepared place to land. That is what
        &ldquo;honestly mapping the unknown&rdquo; means, and we believe it is
        the durable contribution: a demonstration that famous open problems can
        be industrialized without being inflated, because the kernel does not
        grade on a curve.
      </p>
      <p
        className="mt-10 text-[0.9rem]"
        style={{ color: "var(--ink-faint)" }}
      >
        Everything on this page is reproducible from{" "}
        <a href="https://github.com/lalalune/ArkLib">lalalune/ArkLib</a>: clone,
        build, and run <code className="inline">#print axioms</code> on any
        theorem named above. The campaign log is public at issues #232, #334,
        #357, and #371.
      </p>
    </Section>
  );
}
