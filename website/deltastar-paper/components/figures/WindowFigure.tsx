/* The window diagram — THE picture of the problem.
   Number line: 0 → UDR → Johnson (1−√ρ) → [open window, hatched] → capacity (1−ρ) → 1 */
export function WindowFigure() {
  const stroke = "var(--ink-secondary)";
  const accent = "var(--accent)";
  const faint = "var(--ink-faint)";
  // positions on a 0..720 axis (rate ρ = 1/4 for legibility: UDR=.375, Johnson=.5, capacity=.75)
  const X = (t: number) => 40 + t * 640;
  const udr = X(0.375);
  const johnson = X(0.5);
  const capacity = X(0.75);
  return (
    <figure className="prose-col my-10">
      <svg
        viewBox="0 0 720 150"
        className="w-full"
        role="img"
        aria-label="The open window for delta-star between the Johnson radius and capacity"
      >
        {/* hatch pattern for the window */}
        <defs>
          <pattern
            id="hatch"
            width="7"
            height="7"
            patternTransform="rotate(45)"
            patternUnits="userSpaceOnUse"
          >
            <line x1="0" y1="0" x2="0" y2="7" stroke={accent} strokeWidth="1.1" opacity="0.5" />
          </pattern>
        </defs>

        {/* main axis */}
        <line x1={X(0)} y1="90" x2={X(1)} y2="90" stroke={stroke} strokeWidth="1.3" />
        {/* arrowhead */}
        <path d={`M ${X(1)} 90 l -9 -4 v 8 z`} fill={stroke} />

        {/* the window band */}
        <rect x={johnson} y="74" width={capacity - johnson} height="32" fill="url(#hatch)" />
        <rect
          x={johnson}
          y="74"
          width={capacity - johnson}
          height="32"
          fill="none"
          stroke={accent}
          strokeWidth="1.2"
        />

        {/* ticks */}
        {[
          { x: X(0), label: "0", sub: "" },
          { x: udr, label: "(1\u2212\u03C1)/2", sub: "unique decoding" },
          { x: johnson, label: "1\u2212\u221A\u03C1", sub: "Johnson radius" },
          { x: capacity, label: "1\u2212\u03C1", sub: "capacity" },
        ].map((t, i) => (
          <g key={i}>
            <line x1={t.x} y1="84" x2={t.x} y2="96" stroke={stroke} strokeWidth="1.3" />
            <text
              x={t.x}
              y="115"
              textAnchor="middle"
              fontSize="13"
              fontFamily="STIX Two Text, serif"
              fill="var(--ink)"
            >
              {t.label}
            </text>
            {t.sub && (
              <text
                x={t.x}
                y="131"
                textAnchor="middle"
                fontSize="10.5"
                fontFamily="IBM Plex Mono, monospace"
                fill={faint}
              >
                {t.sub}
              </text>
            )}
          </g>
        ))}

        {/* proven regions annotations */}
        <text
          x={(X(0) + johnson) / 2}
          y="62"
          textAnchor="middle"
          fontSize="11"
          fontFamily="IBM Plex Mono, monospace"
          fill={faint}
        >
          proven safe (MCA holds)
        </text>
        <text
          x={(capacity + X(1)) / 2 + 8}
          y="62"
          textAnchor="middle"
          fontSize="11"
          fontFamily="IBM Plex Mono, monospace"
          fill={faint}
        >
          provably broken
        </text>

        {/* the window label */}
        <text
          x={(johnson + capacity) / 2}
          y="36"
          textAnchor="middle"
          fontSize="13.5"
          fontFamily="STIX Two Text, serif"
          fontStyle="italic"
          fill={accent}
        >
          {"\u03B4* lives here \u2014 exact location unknown"}
        </text>
        <line
          x1={(johnson + capacity) / 2}
          y1="42"
          x2={(johnson + capacity) / 2}
          y2="70"
          stroke={accent}
          strokeWidth="1"
          strokeDasharray="3 3"
        />
      </svg>
      <figcaption
        className="mt-2 text-[0.85rem]"
        style={{ color: "var(--ink-faint)" }}
      >
        Figure 1. The state of knowledge for smooth Reed&ndash;Solomon codes (drawn
        at rate ρ = 1/4). Below the Johnson radius, mutual correlated agreement
        is proven. Above capacity, it provably fails. The hatched window is the
        prize question.
      </figcaption>
    </figure>
  );
}
