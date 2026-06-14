# RESOLUTION: the #400 combinatorial-closure route is REFUTED — reduces back to the char-sum wall (#407) (2026-06-13)

Grinding the #400 extremality "until proven or refuted" — **REFUTED as a closure**, corroborated by the
owner's independent exact enumeration (#400/#407 comments).

## The refutation (owner + my findings agree)
The MCA bad-scalar count `|B| = n·#orbits` is **super-linear**, NOT O(n) and NOT a clean closed count:
- Owner exact cyclotomic enumeration: `#orbits` grows `3 → 23` (n=16→32) at fixed rate ρ=7/16
  (k=Θ(n)); `|B|: 48 → 608`, ~12.7× per doubling ⟹ `|B| ~ n^{2.7+}` (super-linear).
- My session findings concur: `s_max` grows (2,3,4,≥6 — I retracted the μ−1 law when n=64 broke it);
  the bad count `Θ(n^{s_max(band)})` has no closed bound; the construction is a lower bound not extremal.
- `#400`'s O(n) form is officially refuted; **issue #400 is superseded by #407**.

## What this means for the session's #400 theory
GENUINE/verified structure (stands): general-direction reduction (bad ⟺ power sums `p_1..p_{m-1}=0`,
readout `p_m=\hat{1_T}(m)`); `e_2=0⟺P(ζ)²=P(ζ²)`; the 2-adic tower recursion `#bad_n(k,2m')=#bad_{n/2}(k/2,m')`;
the CLOSED m=2 binomial `Σ_s C(N/2,s)2^s` (no additive energy). These are real, correct results about the
SHALLOW (small-m / near-capacity) bands and the dir(k,t) family.
BUT the CLOSURE FAILS: the prize δ* sits at DEEP bands where (i) the worst direction is the large-gap
construction with super-linearly-many bad scalars, and (ii) the count does not admit a closed
combinatorial extremality — it carries the same content as the character-sum bound. The m=2
no-additive-energy result was a genuine but shallow special case; it does NOT extend to closure.

## The actual open core (back to #407, the recognized-hard wall)
δ* closure reduces to **`M(n) = max_{b≠0} |Σ_{x∈μ_n} e_p(bx)| ≤ n^{1/2+o(1)}`** — the BGK incomplete-
subgroup-sum / square-root-cancellation bound (SOTA `n^{1−1/2880}`, Kowalski 2024; sum-product + BSG).
This is exactly the wall identified early this session ([[issue389-deltastar-proven-scaffold-2026-06-13]]):
the char-sum face. The #400 combinatorial route does NOT escape it; it reduces back to it at the deep bands.

## Honest final verdict (proven/refuted as requested)
- **REFUTED:** "the #400 combinatorial count closes δ* / is O(n) / has a closed extremality." The count is
  super-linear; no closed combinatorial δ* exists via this route.
- **STANDS (verified):** the structural reduction, the recursion, the m=2 closed formula — as correct
  results about the shallow bands, not a closure.
- **OPEN (the real core, #407):** `M(n) ≤ n^{1/2+o(1)}` (BGK square-root cancellation) — recognized-hard,
  the same wall. δ* = 1−ρ−Θ(1/log n) is the conjectured answer, pinned to this bound.

The grind reached a definitive answer: the combinatorial-escape hypothesis is refuted; the prize core is
the character-sum √-cancellation bound, not closed combinatorics. No fabricated closure.
