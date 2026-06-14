# The prize deficit is QUANTIFIED: n^{1/6}, not n^{1/2} — base-field large-subgroup k-th-power Gauss sum at the joint worst spot, 2026-06-14

## Definitive result (two high-confidence tracks agree)

The reclassification (prize domain = base-field LARGE subgroup `n=p^{0.678}`, index `d=(p−1)/n≈p^{1/3}`,
over the 31-bit KoalaBear base prime — NOT a thin extension subgroup) is **correct and favorable but
does not close the prize**. Precise accounting at the §6.3 prize point (`p=2^31−2^24+1`, `n=2^21`, `d=1016`):

| quantity | exponent | value |
|---|---|---|
| **best PROVEN** (Weil/Gauss triangle, MVW-sharpened) | `n^{0.738}` = `√p` | `0.707√p ≈ 32√n` |
| **target** `√(n·log(p/n))` (δ* formula exact) | `n^{0.567}` | `2.63√n` |
| **conjectural truth** (= numerically measured) | `n^{0.500}` | `√(p/d)=√n` |

The deficit (proven vs target) is the factor `√(d/log(p/n)) = √(1016/6.92) ≈ 12 = p^{1/6} = n^{0.17}`.

## The advance: deficit n^{1/6}, not n^{1/2}

Under the OLD (wrong) thin-extension reading (`q=2^186`, `n~q^{1/4}`), the deficit was a **full
half-power** `n^{1−o(1)}` (the di-Benedetto-vanishes / Paley wall — essentially hopeless). The CORRECT
base-field large-subgroup reading shrinks the deficit to **`n^{1/6}`** — a factor of ~12, the
√-cancellation among `d≈1016` `k`-th-power Gauss sums. This is a **dramatically smaller, sharply
quantified gap**, and it is the honest localization of the prize.

## The exact open statement (fully localized)

`|G(a)| = |Σ_x e_p(a x^d)| ≤ C√d·√p·polylog` (instead of trivial `(d−1)√p`), for `d ≈ p^{1/3}`,
equivalently `M(n) ≤ C√(n·log(p/n))` for the order-`n=(p−1)/d` subgroup with `n > p^{1/2}`. Square-root
cancellation among `d ≈ p^{1/3}` Gauss sums.

## Why it is still open (the near-miss)

Heath–Brown–Konyagin 2000 prove nontrivial `k`-th-power Gauss-sum bounds (`k^{5/8}p^{5/8}` etc.) **only
for `p^{1/3} < k < p^{2/3}`**. The prize `d=1016` sits **just below** `p^{1/3}=1287` (`n=2^21` just above
`p^{2/3}=2^{20.67}`) — it **misses the favorable HBK range by a hair**, landing exactly at the joint worst
spot where the trivial `√p` bound and all power-saving bounds coincide. Even HBK's range gives only
`n^{0.44−0.74}`, never `n^{1/2+o(1)}`; Shkredov's medium-size bound needs `n∈(p^{0.37},p^{0.60})` (prize
`n=p^{0.68}` is above it); di-Benedetto/BGK need `n<p^{1/2}` (thin, inapplicable). So **no published
result crosses `n^{1/2+o(1)}` for `n>p^{1/2}`** — but the gap is now `n^{1/6}`, not `n^{1/2}`.

## Honest net

- **Proven unconditional:** index `d=2` (quadratic) reaches `√n/√2` exactly; constant `d` gives `O(√n)`.
- **The prize residual:** `√d≈32`-fold cancellation needed, `√(d/log)≈12`-fold deficit = `n^{1/6}`, at the
  HBK joint-worst-spot `d~p^{1/3}`. This is a recognized-hard but FAR more localized problem than the thin
  Paley wall — a factor `n^{1/6}` cancellation, not `n^{1/2}`.
- Both grand challenges still reduce to this single bound; it is genuinely open. But the reclassification
  is a real contribution: it correctly identifies the regime and shrinks the proven-vs-target gap from a
  half-power to `n^{1/6}`, and pinpoints the near-miss of the HBK favorable range.

Probes: this session's M(n) measurements (large vs thin), moment-bound-at-shallow-depth, base-field
collapse. Papers: HeathBrownKonyagin-2000, di-Benedetto 2003.06165, Kowalski 2401.04756, Shkredov 1311.5726.
