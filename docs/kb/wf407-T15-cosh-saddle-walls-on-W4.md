# T15-cosh: the cosh-MGF root-free saddle inequality WALLS onto W4 (deep-moment wall)

**Thread:** 407-T15 / A03 (`UNFINISHED_THREADS_407.md` Cluster 1, status `open/yes`, rel 6 feas 3).
**Date:** 2026-06-14. **Verdict: WALLED to W4** (the deep-moment / `√(log)`-short wall,
`CharSumMomentDeepWall.lean`). Honest — no closure.

## The route (recap)

Open core: worst Gauss period `B = max_{b≠0} ‖η_b‖`, `η_b = Σ_{x∈μ_n} e_p(bx)`; conjectured floor
`B ≤ √(2 n log(q/n))`. The cosh route uses the EXACT char-0 identity

  `Σ_{b∈F_p} cosh(‖η_b‖ y) = p · I₀(2y)^{n/2}`   (char-0, exact)

to get the ROOT-FREE one-term bound `B ≤ min_y (1/y) arccosh(p · I₀(2y)^{n/2})`. The saddle
`y* = √(2 log p / n)` gives `B ≤ √(2 n log 2p)(1+o(1))` — empirically tighter than the moment method
(8.56 vs 9.99 in the prior A03 note). The thread asked: is this a NEW attack, or does it collapse to W4?

## The three questions, settled by numerics (exact, enumerable)

Probes: `scripts/probes/wf407_T15-cosh_saddle_verdict.py` (Q1/Q2),
`scripts/probes/wf407_T15-cosh_Q3_saddle_weight.py` (Q3, analytic/log-space).

**Q1 — the identity is CHAR-0, not char-p.** The cosh identity holds EXACTLY (ratio LHS/RHS =
1.00000) at small `y`, but the ratio diverges above 1 at large `y`, with onset depending on `p/n`:
- n=8, p=257 (β≈4.0): ratio 1.00 → 1.014 (y=1.0) → 1.41 (y=2.0).
- n=16, p=65537 (β=4.0): 1.00 → 1.044 (y=1.0) → 2.93 (y=2.0).
- n=32, p=1048609 (β≈4.0): 1.00 → 1.50 (y=0.6) → **71.6** (y=1.0) → 3226 (y=1.5).
The b≠0 part (`Σ_{b≠0}cosh − cosh(ny) − char-0 prediction`) shows the SAME excess (n=32: ratio 2.03
at y=0.6). This divergence IS the char-p mod-`p` coincidence excess `E_r^{(p)} − E_r^∞ ≥ 0`. The
RHS `p I₀(2y)^{n/2}` is therefore NOT an upper bound on the true char-p LHS in the relevant `y`-range.

**Q2 — the cosh envelope is a REPACKAGING of the moments (collapse).** Computing the TRUE char-p
cosh bound `cosh_p = min_y (1/y) arccosh(Σ_{b≠0} cosh(‖η_b‖y))` against the best single moment
`mom_p = min_r (Σ_{b≠0}‖η_b‖^{2r})^{1/2r}`: `cosh_p / mom_p ∈ [1.019, 1.043]` across (n,p) — the
cosh envelope is essentially EQUAL to (slightly WORSE than) the best single moment. `cosh = Σ even
moments`, so the MGF carries exactly the same information; the "root-free" form is cosmetic.

**Q3 — the saddle lands a/2 tower-levels TOO DEEP (the decisive new fact).** After the PROVEN Bessel
baseline `E_r ≤ (2r−1)!!·n^r = (2r)! n^r/(2^r r!)` (`RungBesselEnergy.lean`), the `r`-th cosh weight is
`w_r(y) = y^{2r}/(2r)!·E_r ≤ (n y²/2)^r / r!` — a **Poisson profile** with intensity `λ = n y²/2`.
At the saddle `y*² = 2 log p / n` the intensity is `λ = log p` EXACTLY, so the dominant weight sits at
`r_peak = ⌊log p⌋`. Confirmed numerically (`r_peak = ⌊log p⌋` to the unit across n=8…2^32) and
`r_peak ≈ r_eff` (the depth the best single moment uses) to within 1. But the char-0 value of `E_r` is
reliable only for `r ≤ r_max = 2 log_n p = 2β`. The peak-to-cap ratio:

  `r_peak / r_max = log p / (2 log_n p) = (log n)/2`  (≈ `0.347·a` for `n = 2^a`).

| n | a | r_peak (=log p) | r_max=2β | ratio |
|---|---|-----------------|----------|-------|
| 8 (β=5) | 3 | 10 | 10 | 1.0 |
| 32 (β=5) | 5 | 17 | 10 | 1.7 |
| 2^16 (β=5) | 16 | 55 | 10 | 5.5 |
| **2^32 (β=5)** | **32** | **111** | **10** | **11.1** |

At the prize `n = 2^32` the saddle samples moments **11× deeper** than the char-0 reliable cap —
exactly the `r_opt/r_max ≍ (log n)/2 = a/2` gap `CharSumMomentDeepWall.lean` records for the RAW
moment method (W4). The cosh-MGF does not escape W4; its saddle automatically selects the same
optimal-but-unreliable depth.

## Why it walls (mechanism)

The cosh-MGF is literally the exponential generating function of the even moments `E_r`. Its saddle
is the Laplace/saddle-point selection of the optimal `r` — which is exactly the `r ≍ log p` the raw
moment method already wants and already cannot reach. The "root-free, no-max" dressing removes the
`2r`-th root and the `max` but moves NONE of the open content: the open content is the validity of
`E_r` at `r ≍ log p`, equivalently a √-cancellation bound on the `(p−1)/n` Gauss-sum phases
`χ̄(b)τ(χ)`, `χ ∈ μ_n^⊥` — the Bourgain/BGK/Paley-graph core. Q1's measured char-p explosion is this
exact defect appearing precisely where the saddle puts its mass.

This is the same diagnosis as `deltastar-moment-method-convergence-diagnosis-2026-06-13.md`: cosh-MGF
joins {energy `E_r`, cyclotomic-norm moments, Salem–Zygmund chaining-via-moments, Lamzouri CLT} as a
fifth member of the moment-method family, all sharing the `r < log_n p` threshold.

## What is PROVEN (axiom-clean Lean, `Frontier/WF407_T15Cosh.lean`)

Audit clean (`[propext, Classical.choice, Quot.sound]`) for all 7 theorems:
- `poissonWeight_succ`: `w_{r+1} = w_r · λ/(r+1)` (the Poisson ratio).
- `poissonWeight_le_succ` / `poissonWeight_succ_le`: weight increases for `r+1 ≤ λ`, decreases for
  `λ ≤ r+1` ⟹ peak at `r ≈ λ` (the concentration fact).
- `saddle_intensity_eq`: at `y² = 2L/n`, `n y²/2 = L` (so `λ = log p` at the saddle).
- `cosh_mgf_walls_on_W4`: `2 log p / log n < log p` for `log n > 2` — the peak strictly exceeds the cap.
- `not_coshSaddleEscapesW4`: the named Prop `CoshSaddleEscapesW4` (`log p ≤ 2 log_n p`, what the route
  would need) is FALSE at every prize `n` (the machine-checked wall, in the wrong direction).
- `peak_over_rmax_eq`: `log p = (log n / 2)·r_max` (quantitative gap = `(log n)/2` tower-levels).

These prove the WALL structure; they do NOT prove the prize. The number-theoretic input (deep-moment
validity at `r ≍ log p`) is deliberately not supplied — it is the W4 open content.

## What remains / spin-offs

The wall is genuine for the cosh route AS A MOMENT METHOD. The one thing the cosh form makes vivid:
the char-p excess (Q1) is sharply LOCALIZED in `y` — it turns on precisely as `y` crosses the saddle.
A correct attack would need a bound on `Σ_{b≠0} cosh(‖η_b‖y)` that is NOT moment-derived (i.e. uses
the actual Gauss-sum phase structure), valid at `y ≥ y*`. That is the same subgroup-Burgess /
effective-equidistribution open problem (`SalemZygmundChaining.SubGaussianMGF`,
`deltastar-407-rojasleon-independence-mgf-verdict`), not a new lever. No thinness-essential structure
is exploited by cosh, so it cannot beat the thickness-monotone barrier (T18) either.

**Cross-refs:** `CharSumMomentDeepWall.lean` (W4), `RungBesselEnergy.lean` (the proven baseline),
`Frontier/SalemZygmundChaining.lean` (the per-coset MGF sibling, same moments),
`deltastar-moment-method-convergence-diagnosis-2026-06-13.md` (the family no-go),
`deltastar-bessel-energy-reduction-2026-06-13.md` (the mod-p excess = the wall).
