# δ* = list size of sparse-support cyclic codes over μ_n (a new lens, #407, 2026-06-14)

## The reformulation (novel framing)
A monomial pencil `x^a+αx^b` agrees with a deg-`<k` codeword `g` on a set `A` (|A|≥(1−δ)n) iff the
vector `x^a+αx^b−g` is a low-weight codeword (weight ≤ δn) of the **sparse-support cyclic code**

  `C'_{a,b} = { c : μ_n → F_q  |  ĉ_j = 0 for j ∉ {0,…,k−1, a, b} }`  (dimension `k+2`),

i.e. evaluations on `μ_n` of polynomials with support `⊆ {0..k−1, a, b}` (a `(k+2)`-sparse poly).
Frobenius is trivial on `μ_n` (`q≡1 mod n`) so all cyclotomic cosets are singletons and `C'` is a
genuine cyclic code with defining set (zeros) `{k..n−1}∖{a,b}`. Hence:

> **`I(δ) = max_{a,b} #{α : x^a+αx^b is δ-close} = max_{a,b} (list size of C'_{a,b} at radius δ)`**,
> and the governing law `δ* = sup{δ: I(δ)≤q·ε*≈n}` becomes a **list-size threshold of sparse-support
> cyclic codes**. This opens the ENTIRE classical cyclic-code toolbox (BCH, Hartmann–Tzeng, Roos,
> van Lint–Wilson, Boston defining-set bounds — all PROVEN) on the prize.

## What it gives (and the honest limit)
- **Min distance `d(C'_{a,b})`** = bottom of the window (first/closest codeword = unique-decoding edge).
  Numerics (n=8, q=521, k=4, ρ=1/2): worst pencil (5,7) has `d=2`, and **BCH=2 is TIGHT** (also tight
  at (6,7): d=3=BCH). So the BCH bound EXACTLY gives the worst-case min distance here — a clean proven
  sub-result for the window bottom `≈ 1 − d/n`.
- **δ\* is NOT `1−d/n`** — that is the unique-decoding edge (first list member). δ\* is where the
  **LIST SIZE** of `C'_{a,b}` crosses the budget `n`, i.e. the **beyond-Johnson list growth** of the
  sparse code (n=8: d=2 ⟹ edge 0.25, but δ\*∈(0.25,0.375) where the list hits the budget; conj 0.39).
  C' has dimension `k+2=ρn+2`, Johnson radius `≈1−√ρ`; δ\* sits ABOVE it. So δ\* = the beyond-Johnson
  list size of sparse-support cyclic codes = the SAME recognized open core (no classical list bound
  is tight beyond Johnson — that is the grand list-decoding challenge itself).

## Verdict
Genuine NEW lens (prize ⟺ list-decoding sparse-support cyclic codes; BCH-tight for the window bottom),
HIGH on novelty/insight/proximity. But feasibility-limited: it reduces δ\* to the beyond-Johnson list
size of these codes, which IS the open grand challenge. Every campaign framing (energy/Bessel, band/
floor, CDD/cumulant, Action-Orbit/orbit-count, now sparse-cyclic-codes) converges to this one core.
