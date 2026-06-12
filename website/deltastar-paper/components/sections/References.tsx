const refs: { id: string; text: string; href?: string }[] = [
  {
    id: "ABF26",
    text: "G. Arnon, D. Boneh, G. Fenzi. Open Problems in List Decoding and Correlated Agreement. IACR ePrint 2026/680. Definition 4.3 is the in-tree \u03b5_mca.",
    href: "https://eprint.iacr.org/2026/680",
  },
  {
    id: "BCIKS20",
    text: "E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf. Proximity Gaps for Reed\u2013Solomon Codes. IACR ePrint 2020/654. Correlated agreement up to the Johnson radius; the \u00a75/Appendix A chain the Johnson lane discharges.",
    href: "https://eprint.iacr.org/2020/654",
  },
  {
    id: "BCHKS25",
    text: "E. Ben-Sasson, D. Carmon, U. Hab\u00f6ck, S. Kopparty, S. Saraf. Proximity gaps stop at the Johnson bound. ECCC TR25-169. The coupling barrier: MCA past Johnson implies beyond-Johnson list decoding.",
    href: "https://eccc.weizmann.ac.il/report/2025/169/",
  },
  {
    id: "KKH26",
    text: "Kambir\u00e9, Kopparty, Hab\u00f6ck (KKH26). IACR ePrint 2026/782. The near-capacity strip exclusion: \u03b4* \u2264 1 \u2212 r/2^\u03bc for explicit smooth evaluation codes.",
    href: "https://eprint.iacr.org/2026/782",
  },
  {
    id: "Hab25",
    text: "U. Hab\u00f6ck. IACR ePrint 2025/2110. The streamlined Johnson-radius MCA lane (the floor of the window).",
    href: "https://eprint.iacr.org/2025/2110",
  },
  {
    id: "CS25",
    text: "A. Crites, A. Stewart. IACR ePrint 2025/2046. With KK25 and DG25: mutual correlated agreement fails at capacity; the reduction coupling upper-bound progress to list decoding.",
    href: "https://eprint.iacr.org/2025/2046",
  },
  {
    id: "DG25",
    text: "B. Diamond, A. Gruen. IACR ePrint 2025/2010. Super-polynomial proximity-gap error at vanishing rate; one of the three independent at-capacity refutations.",
    href: "https://eprint.iacr.org/2025/2010",
  },
  {
    id: "GS99",
    text: "V. Guruswami, M. Sudan. Improved decoding of Reed\u2013Solomon and algebraic-geometry codes. IEEE Trans. Inform. Theory 45 (1999). List decoding to the Johnson radius \u2014 the engine behind every in-tree polynomial list bound, and the 25-year boundary.",
  },
  {
    id: "GZ23",
    text: "Z. Guo, Z. Zhang. Randomly punctured Reed\u2013Solomon codes achieve list-decoding capacity over polynomial-size alphabets. arXiv:2304.01403 (FOCS 2023 line).",
    href: "https://arxiv.org/abs/2304.01403",
  },
  {
    id: "CZ25",
    text: "Y. Chen, Z. Zhang. Explicit folded Reed\u2013Solomon codes achieve capacity with optimal list size. STOC 2025. Why folding works and the plain smooth domain resists.",
  },
];

export function References() {
  return (
    <section id="references" className="prose-col mt-20">
      <h2 className="text-[1.45rem] font-semibold mb-6">References</h2>
      <ol className="refs list-none pl-0 space-y-3">
        {refs.map((r) => (
          <li key={r.id} id={`ref-${r.id}`}>
            <span
              className="mono text-[0.8rem] mr-2"
              style={{ color: "var(--accent)" }}
            >
              [{r.id}]
            </span>
            {r.text}{" "}
            {r.href ? (
              <a
                href={r.href}
                className="text-[0.85rem]"
                style={{ color: "var(--ink-faint)" }}
              >
                {r.href.replace("https://", "")}
              </a>
            ) : null}
          </li>
        ))}
      </ol>
      <p className="mt-8 text-[0.85rem]" style={{ color: "var(--ink-faint)" }}>
        Seventeen papers are wired into the formalization in total; the
        complete inventory with in-tree consumers is{" "}
        <a href="https://github.com/lalalune/ArkLib/blob/main/docs/kb/deltastar-research-map.md">
          <code>docs/kb/deltastar-research-map.md</code>
        </a>
        .
      </p>
    </section>
  );
}
