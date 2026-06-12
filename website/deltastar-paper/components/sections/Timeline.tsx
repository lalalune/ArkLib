const items: { label: string; text: string; muted?: boolean }[] = [
  {
    label: "Issue #232",
    text: "The disproof campaign: attack the ABF26 Grand Challenge conjecture itself, keep every constraint lemma. 23 verified bricks; the Johnson-threshold carving matches what the literature later confirmed.",
    muted: true,
  },
  {
    label: "Nov 2025",
    text: "Three independent groups refute the at-capacity conjectures (CS25, KK25, DG25). The window becomes the problem. The refutations are formalized in-tree.",
    muted: true,
  },
  {
    label: "Issue #357 opens",
    text: "Two parallel nine-hypothesis slates under the standing discipline: constraints, why-nobody, larp-check, falsification probe, then formalize.",
  },
  {
    label: "First pin",
    text: "\u03b4*(RS[F\u2085, F\u2085\u02e3, 2], 2/5) = 1/4 \u2014 the first exact MCA threshold for any code, landed in two independent lanes within hours of each other.",
  },
  {
    label: "The staircase",
    text: "Band collapse at b = 2, then b = 3, then all bands at the 3b\u22122 threshold \u2014 sharpened from 4j to 3j during formalization. The MDS rank conjecture dies by pencil explosion; 3b\u22122 is the law.",
  },
  {
    label: "The census programme",
    text: "Bad scalars become subset-sum combinatorics; the wide-circuit matroid census closes with a machine-generated 1,571-line converse proof emitted from 10,395 probe certificates.",
  },
  {
    label: "The Johnson lane",
    text: "The BCIKS20 \u00a75 discharge chain driven to a single named residual through two machine-checked corrections of the paper's own recursion (findings 13 and 14).",
  },
  {
    label: "Issue #371: the WB programme",
    text: "Badness becomes pencil linear algebra. Six theorems close the below-UDR branches; the window adversary is found and is M\u00f6bius-symmetric; PGL\u2082 equivariance is proven.",
  },
  {
    label: "The unification",
    text: "The ownership bound contains both lanes as instances. The k = 1 window closes unconditionally by direction class: polynomial (zero), rational (multiplicity theorem), sparse (popularity).",
  },
  {
    label: "Today",
    text: "The frontier is formalized; the open core is three named Props and four equivalent faces. The window at production rate is open.",
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
