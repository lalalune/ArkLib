/* Swarm motif — many agents, one wall, honest casualties. Abstract + geometric. */
export function SwarmFigure() {
  const faint = "var(--ink-faint)";
  const accent = "var(--accent)";
  const verified = "var(--verified)";
  // deterministic pseudo-random dot field (no Math.random — stable SSR)
  const dots: { x: number; y: number; dead?: boolean }[] = [];
  let seed = 7;
  const rnd = () => {
    seed = (seed * 16807) % 2147483647;
    return seed / 2147483647;
  };
  for (let i = 0; i < 64; i++) {
    const x = 30 + rnd() * 330;
    const y = 28 + rnd() * 124;
    dots.push({ x, y, dead: rnd() < 0.3 });
  }
  return (
    <figure className="prose-col my-10">
      <svg
        viewBox="0 0 640 180"
        className="w-full max-w-xl mx-auto"
        role="img"
        aria-label="A swarm of agents against the wall; refuted attempts marked, verified bricks passing through"
      >
        {/* the wall */}
        <line x1="420" y1="16" x2="420" y2="164" stroke="var(--ink)" strokeWidth="2.5" />
        <text x="420" y="10" textAnchor="middle" fontSize="10.5" fontFamily="IBM Plex Mono, monospace" fill={faint}>
          the open core
        </text>

        {/* swarm */}
        {dots.map((d, i) =>
          d.dead ? (
            <g key={i} opacity="0.55">
              <line x1={d.x - 3} y1={d.y - 3} x2={d.x + 3} y2={d.y + 3} stroke={accent} strokeWidth="1.2" />
              <line x1={d.x - 3} y1={d.y + 3} x2={d.x + 3} y2={d.y - 3} stroke={accent} strokeWidth="1.2" />
            </g>
          ) : (
            <circle key={i} cx={d.x} cy={d.y} r="2.4" fill={faint} opacity="0.8" />
          )
        )}

        {/* verified bricks that made it through the wall */}
        {[40, 72, 104, 136].map((y, i) => (
          <g key={i}>
            <line
              x1="400"
              y1={y + 20}
              x2="436"
              y2={y + 20}
              stroke={verified}
              strokeWidth="1"
              strokeDasharray="2 3"
              opacity="0.7"
            />
            <rect x="438" y={y + 15} width="11" height="11" fill="none" stroke={verified} strokeWidth="1.4" />
          </g>
        ))}
        <text x="500" y="95" fontSize="10.5" fontFamily="IBM Plex Mono, monospace" fill={verified}>
          axiom-clean theorems
        </text>

        {/* legend */}
        <g transform="translate(34, 168)">
          <circle cx="0" cy="-3" r="2.4" fill={faint} />
          <text x="8" y="0" fontSize="10" fontFamily="IBM Plex Mono, monospace" fill={faint}>
            live hypothesis
          </text>
          <line x1="118" y1="-6" x2="124" y2="0" stroke={accent} strokeWidth="1.2" />
          <line x1="118" y1="0" x2="124" y2="-6" stroke={accent} strokeWidth="1.2" />
          <text x="130" y="0" fontSize="10" fontFamily="IBM Plex Mono, monospace" fill={faint}>
            refuted (kept as constraint lemma)
          </text>
        </g>
      </svg>
      <figcaption className="mt-2 text-[0.85rem]" style={{ color: "var(--ink-faint)" }}>
        Figure 3. The campaign, abstractly: hypotheses swarm the wall; refuted
        ones are kept as machine-checked constraint lemmas; what passes the
        kernel lands as axiom-clean theorems on the other side.
      </figcaption>
    </figure>
  );
}
