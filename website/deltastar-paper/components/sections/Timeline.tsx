const items: { label: string; text: string; muted?: boolean }[] = [
  {
    label: "Issue #232",
    text: "The disproof-first phase: the ABF26 grand-challenge conjecture is attacked directly and every surviving constraint is kept as a lemma. Twenty-three verified results; the Johnson-threshold carving agrees with what the literature later confirmed.",
    muted: true,
  },
  {
    label: "Nov 2025",
    text: "Three independent groups refute the at-capacity conjectures (CS25, KK25, DG25). The beyond-Johnson window becomes the problem. The refutations are formalized in-tree.",
    muted: true,
  },
  {
    label: "Issue #357",
    text: "Two parallel nine-hypothesis slates under the standing discipline: enumerate constraints, identify why the question resisted prior methods, screen for vacuity, run a falsification probe, then formalize what survives.",
  },
  {
    label: "First exact pin",
    text: "\u03b4*(RS[F\u2085, F\u2085\u02e3, 2], 2/5) = 1/4, the first exact MCA threshold computed for any code, obtained in two independent lanes within hours of each other.",
  },
  {
    label: "The staircase",
    text: "Band collapse at b = 2, then b = 3, then all bands at the 3b\u22122 threshold, sharpened from 4j to 3j during formalization. The MDS rank conjecture is refuted by an explicit pencil countermodel; 3b\u22122 is the law.",
  },
  {
    label: "The census programme",
    text: "Bad scalars are recast as subset-sum combinatorics; the wide-circuit matroid census closes with a machine-generated 1,571-line converse proof emitted from 10,395 exact probe certificates.",
  },
  {
    label: "The Johnson lane",
    text: "The BCIKS20 \u00a75 discharge chain is driven to a single named residual through two machine-checked corrections of the source paper's own recursion (findings 13 and 14).",
  },
  {
    label: "Issue #371",
    text: "Badness is recast as pencil linear algebra. Six theorems close the below-unique-decoding branches; the window adversary is identified and shown M\u00f6bius-symmetric; PGL\u2082 equivariance is proven.",
  },
  {
    label: "The unification",
    text: "The ownership bound contains both lanes as instances. The k = 1 window closes unconditionally by direction class: polynomial (zero), rational (a multiplicity theorem), and sparse (a popularity bound).",
  },
  {
    label: "The reduction to CORE",
    text: "The open core is reduced, by machine-checked in-tree reductions, to a single explicit inequality (CORE): \u221an cancellation for incomplete character sums over the thin 2-power subgroup. This is the classical BGK / Paley wall, located to the exponent (gap 0.489).",
  },
  {
    label: "Impossibility results",
    text: "The moment-method no-go is proven: every energy / Parseval / spectral route caps at the Johnson radius, the moment ladder overshoots the target at every depth, and thinness is shown necessary (CORE is false in the thick regime). Three closure claims were self-retracted in the same pass; the ledger self-corrects.",
  },
  {
    label: "Current state",
    text: "The reduction side is essentially complete and machine-checked. The floor question reduces to one open combinatorial crossing, and the residual analytic difficulty is the recognized two-decade-open CORE inequality; naming the wall does not shorten it. The window at production rate remains open, at one precise classical sentence.",
  },
];

export function Timeline() {
  return (
    <section id="timeline" className="prose-col mt-20">
      <h2 className="sc-label text-[0.95rem] font-semibold mb-8">
        Campaign timeline
      </h2>
      <div className="timeline">
        {items.map((it) => (
          <div
            key={it.label}
            className={`timeline-item${it.muted ? " muted" : ""}`}
          >
            <p
              className="sc-label text-[0.8rem] font-semibold"
              style={{ color: it.muted ? "var(--ink-faint)" : "var(--accent)" }}
            >
              {it.label}
            </p>
            <p
              className="mt-1 text-[0.92rem]"
              style={{ color: "var(--ink-secondary)" }}
            >
              {it.text}
            </p>
          </div>
        ))}
      </div>
    </section>
  );
}
