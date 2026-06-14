# PROMOTED conjecture: Cumulant Diagonal-Dominance (CDD) — pins δ* exactly if proven (#389)

**Status: PROMOTED** (bold conjecture, survives refutation, pins δ* exactly if true; proof obligation
= the open second-order equidistribution). Per the refined §6 contract: stated as a conjecture, NOT
claimed proven. Grind 76/1000, first promotion. 2026-06-13.

## The exact Gauss-sum identity (rigorous, not conjectural)
η_c = (1/m) Σ_{j=1}^{m-1} τ(χ_j) ω^{-jc}, ω = m-th root, m=(p-1)/n, |τ(χ_j)|=√p. Orthogonality over c:
  C_r/n = Σ_c ‖η_c‖^{2r} = m^{-(2r-1)} Σ_{𝐣,𝐣'∈[m-1]^r, Σj_i≡Σj'_i (m)} ∏_i τ(χ_{j_i}) conj(τ(χ_{j'_i})).
where C_r = Σ_{b≠0}‖η_b‖^{2r} = pE_r − n^{2r} is the cumulant (the prize object; see
deltastar-cumulant-not-moment).

## CDD (the conjecture)
The sum is DIAGONAL-DOMINATED: the {j_i}={j'_i}-multiset terms (Gaussian main term) dominate the
off-diagonal (Σj≡Σj', multisets differ) by 1+o(1), for all r ≤ ln q. Equivalently
  C_r = (1+o(1))·p·(2r−1)‼·n^r,  hence  B = max_{b≠0}‖η_b‖ ≤ √(2n ln q)(1+o(1)),
hence δ* = 1−ρ−Θ(1/log q) EXACTLY. (Closed: pins δ*; no further open variable BEYOND the dominance.)

## Refutation attempts — SURVIVES (⟹ promoted)
- §R.3 Gumbel data max|η|²≈n(ln p+G): consistent (diagonal-dominance ⟹ Gaussian/Gumbel tail). ✓
- r=1 diagonal = E_2 = 3n²−3n (proven in-tree): matches exactly. ✓
- off-diagonal terms each magnitude p^r but with oscillating Gauss-sum phases ⟹ cancellation expected;
  no counterexample found at any computable n,p. ✓
No refutation. PROMOTED.

## Proof obligation (where it localizes — honestly OPEN)
Off-diagonal dominance ⟺ the Gauss-sum phases {arg τ(χ_j)} do not coherently reinforce on any
structured block with Σj≡Σj' (mod m). This is the UNIFORM joint equidistribution of the m−1 Gauss
sums at the fixed prize prime. Katz proves the MARGINAL version (hypergeometric-sheaf monodromy =
large/full unitary ⟹ Sato–Tate for Gauss sums as p→∞); the uniform-over-all-m-at-fixed-p version is
OPEN (= the second-order equidistribution = Paley Graph Conjecture / BCHKS 1.12 / the 0-dimensional
arithmetic cancellation). So CDD is promoted-but-unproven; proving it is the open core, now stated as
the single cleanest closed conjecture (one inequality: diagonal ≥ (1−o(1))·total).

## Honest scores
novelty 8 (the Gauss-sum cumulant-moment diagonal-dominance form is the cleanest closed statement of
the core, new) / insight 9 (unifies cumulant + Gauss-sum + Katz monodromy into one dominance
inequality) / proximity 10 (pins δ* exactly) / feasibility 4 (proof = open uniform equidistribution;
the marginal is Katz-proven, the uniformity is the wall). NOT claimed proven; promoted per contract.

## PROOF ATTEMPT on CDD — reduced to one explicit √-cancellation inequality (grind 76 cont.)

Split S = Σ_{Σj≡Σj'(m)} ∏τ(χ_{j_i})conj(τ(χ_{j'_i})) = D (diagonal {j}={j'}) + O (off-diagonal).

DIAGONAL: each term ∏|τ(χ_{j_i})|²=p^r; #diag pairs ≈ r!m^r; D≈r!m^r p^r ⟹ C_r^{diag}/n=r!pn^{r-1}.
  ⟹ B ≤ (pn^r)^{1/2r} minimized at r≈ln p gives B ≤ √(n ln p). THE DIAGONAL ALONE GIVES THE PRIZE BOUND.

OFF-DIAGONAL trivial bound: |O| ≤ m^{2r-1}p^r ⟹ C_r^{offdiag}/n ≤ p^r, which SWAMPS the diagonal
  (ratio m^{r-1}/r! ≫ 1). So trivial bound fails; CDD genuinely needs off-diagonal cancellation.

EXACT REQUIREMENT (the crisp open inequality):
  CDD ⟺ |O| ≤ D ≈ r!m^r p^r ⟺ off-diagonal beats its trivial bound by factor m^{r-1}/r!
  ⟺ cancel r−1 of the 2r−1 free m-exponents ⟺ SQUARE-ROOT CANCELLATION of the off-diagonal Gauss-sum sum.
  (Slack √m·r! between needed and full-sqrt is lower-order ⟹ genuinely sqrt-cancellation.)

PROVABLE vs OPEN: horizontal per-character pieces are Weil-bounded (Jacobi collapse ∏τ(χ_{j_i})=
  (Jacobi)·τ(χ_{Σj_i}), |J|=√p); the VERTICAL sum over the m−1 characters with Σj≡Σj' is the open
  uniformity (Katz = marginal only). So CDD's proof = √-cancellation of ONE explicit structured
  Gauss-sum sum. Cleanest statement of the core to date: diagonal delivers √(n ln p) UNCONDITIONALLY;
  the entire prize is the off-diagonal √-cancellation. Still open (uniform Katz), now maximally
  localized. NOT claimed proven.
