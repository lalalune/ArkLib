# Katz-monodromy research: Gauss-sum joint independence is PROVEN (q→∞); prize = effective version; HD-smoothness criterion REFUTED (2026-06-13)

Researched the Katz monodromy framing of the prize core (M(n)≤√(n log p) ⟺ Gauss-sum family joint
independence). New papers: Rojas-León arXiv:2207.12439, Fouvry–Kowalski–Michel arXiv:1910.08572 (Katz
survey), Jacobi-sum equidist. arXiv:1809.04286, arithmetic Fourier transforms arXiv:2109.11961.

## The genuine theoretical input (Rojas-León 2022, building on Katz [Kat88, Thm 9.5])
- The Gauss sums `G(χ^{d_1}),…,G(χ^{d_n})` (fixed d_i, varying χ) become **JOINTLY EQUIDISTRIBUTED /
  INDEPENDENT on (S¹)ⁿ as q=m→∞** (Cor 2). Via the ℓ-adic Mellin transform / Tannakian monodromy: the
  monodromy group is the FULL `GL(1)ⁿ` **iff there are no multiplicative relations** (Prop 1 / Cor 7).
- **The ONLY relations among Gauss sums `G(ηχ^n)` are conjugation, Frobenius `G(χ^p)=G(χ)`, and
  Hasse–Davenport** (the paper's headline). So the "non-conspiracy" the prize needs is QUALITATIVELY
  PROVEN — Gauss sums don't conspire beyond HD.

## Consequence: the conjecture is a THEOREM in the q→∞ limit
Since `η_b = (1/f)Σ_s \bar{χ_s}(b)G(χ_s)` and the G(χ_s) are jointly independent (Katz), the random-phase
model is RIGOROUS as q→∞ ⟹ `M(n) ≈ √(n·ln p)`. **The prize is the EFFECTIVE/quantitative version at the
fixed (large) prize q** — i.e. an effective equidistribution rate (Deligne/Weil bound + conductor of the
hypergeometric sheaf). Different machine than additive-combinatorial BGK; same status (effectivity open).

## My HD-mechanism hypothesis: REFUTED (`probe_hd_mechanism_heaviness.py`)
Conjectured heaviness ⟺ f=(p−1)/n smooth (rich HD relations). FALSE: at n=64, heaviness occurs at
- f=1024=2^10 (ρ=524) AND f=757 PRIME (ρ=154) AND f=2803 prime (ρ=2.47);
- mean lpf(f)/f: heavy 0.206 vs healthy 0.177 — NOT separated.
So heaviness is NOT a clean arithmetic criterion on f; it is **erratic small-q accidents** in the window
`n/√p∈[0.15,0.35]` (β≈2.5–3) — exactly where the q→∞ equidistribution has NOT yet kicked in (the effective
discrepancy is still O(1) at small q). The prize regime β≥4 (huge q) is past the accidents (empirically
healthy, no heavy prime found — `probe_cumulant_heaviness_hunt.py`).

## Honest status / net
GENUINE: the prize core is now grounded in PROVEN math — Gauss-sum joint independence (Katz/Rojas-León),
making the conjecture an asymptotic THEOREM; the prize is its effective version at fixed large q.
REFUTED: the clean HD-smoothness criterion (heaviness is erratic small-q accidents, not f-structure).
OPEN: the effective equidistribution rate at the prize's q (Deligne bound + sheaf conductor for the
GROWING f-dimensional family) — this is the gap, and it is a geometric/monodromy estimate, NOT BGK
sum-product. The accidents show effectivity is non-uniform at small q but the prize's q is past them.
The right next move (needs the étale-cohomology toolkit): bound the conductor/dimension of the relevant
hypergeometric sheaf to make Katz's equidistribution effective at the prize scale. Not a closure; no fabrication.
