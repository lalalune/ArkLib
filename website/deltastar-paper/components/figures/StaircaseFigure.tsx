/* Staircase figure — δ*(ε*) = j/n on the granularity bands. */
export function StaircaseFigure() {
  const stroke = "var(--ink-secondary)";
  const accent = "var(--accent)";
  const faint = "var(--ink-faint)";
  const steps = 5;
  const x0 = 60;
  const y0 = 150;
  const w = 96;
  const h = 22;
  return (
    <figure className="prose-col my-10">
      <svg
        viewBox="0 0 640 200"
        className="w-full max-w-xl mx-auto"
        role="img"
        aria-label="The delta-star staircase: delta-star equals j over n on each granularity band"
      >
        {/* axes */}
        <line x1={x0} y1={y0} x2={x0 + steps * w + 30} y2={y0} stroke={stroke} strokeWidth="1.2" />
        <line x1={x0} y1={y0} x2={x0} y2={y0 - steps * h - 25} stroke={stroke} strokeWidth="1.2" />
        <path d={`M ${x0 + steps * w + 30} ${y0} l -8 -3.5 v 7 z`} fill={stroke} />
        <path d={`M ${x0} ${y0 - steps * h - 25} l -3.5 8 h 7 z`} fill={stroke} />

        {/* staircase */}
        {Array.from({ length: steps }).map((_, j) => {
          const xa = x0 + j * w;
          const xb = x0 + (j + 1) * w;
          const y = y0 - (j + 1) * h;
          return (
            <g key={j}>
              {/* riser (dashed, open at band edge) */}
              {j > 0 && (
                <line
                  x1={xa}
                  y1={y0 - j * h}
                  x2={xa}
                  y2={y}
                  stroke={accent}
                  strokeWidth="1"
                  strokeDasharray="2.5 3"
                  opacity="0.6"
                />
              )}
              {/* tread */}
              <line x1={xa} y1={y} x2={xb} y2={y} stroke={accent} strokeWidth="2.2" />
              {/* closed left endpoint, open right endpoint */}
              <circle cx={xa} cy={y} r="2.8" fill={accent} />
              <circle cx={xb} cy={y} r="2.8" fill="var(--paper)" stroke={accent} strokeWidth="1.4" />
            </g>
          );
        })}

        {/* labels */}
        <text x={x0 + (steps * w) / 2} y={y0 + 30} textAnchor="middle" fontSize="13" fontFamily="STIX Two Text, serif" fill="var(--ink)">
          {"\u03B5* (in units of 1/q)"}
        </text>
        <text
          x={x0 - 14}
          y={y0 - (steps * h) / 2}
          textAnchor="middle"
          fontSize="13"
          fontFamily="STIX Two Text, serif"
          fill="var(--ink)"
          transform={`rotate(-90 ${x0 - 14} ${y0 - (steps * h) / 2})`}
        >
          {"\u03B4*"}
        </text>
        {[1, 2, 3].map((j) => (
          <text
            key={j}
            x={x0 + j * w - w / 2}
            y={y0 - j * h - 8}
            textAnchor="middle"
            fontSize="11"
            fontFamily="IBM Plex Mono, monospace"
            fill={faint}
          >
            {j === 3 ? "\u22EF j/n" : `${j}/n`}
          </text>
        ))}
      </svg>
      <figcaption className="mt-2 text-[0.85rem]" style={{ color: "var(--ink-faint)" }}>
        Figure 2. The granularity staircase: on each band ε* ∈ [j/q, (j+1)/q),
        the threshold is exactly δ* = j/n (closed on the left, open on the
        right) — proven for every smooth RS instance in the ladder regime,
        including at the literal prize budget ε* = 2⁻¹²⁸.
      </figcaption>
    </figure>
  );
}
