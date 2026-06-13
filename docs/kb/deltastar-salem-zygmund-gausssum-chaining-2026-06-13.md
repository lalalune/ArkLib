# The δ* prize as a Salem–Zygmund bound for the Gauss-sum trigonometric polynomial (#389)

**Status:** novel route to the open core, cross-field (analytic NT × probability/random-trig-poly ×
generic chaining). Refutation-tested (survives), honestly scored. NOT a closure — the residual is
reframed into a classical, better-tooled object. Author: δ* lane, 2026-06-13.

## The exact identity (proven, elementary)

For `μ_n ⊂ F_p^×`, `n=2^k`, `p≡1 (mod n)`, `m=(p−1)/n`, generator `g`, the Gaussian periods
`η_c = Σ_{x∈μ_n} e_p(g^c x)` (`c∈ℤ/m`) decompose via the `m−1` nontrivial characters `χ_j` of
`F_p^×/μ_n ≅ ℤ/m` (Gauss sums `τ(χ_j)`, `|τ(χ_j)|=√p`):

> **`η_c = −1/m + (1/m) Σ_{j=1}^{m−1} τ(χ_j) · e(−jc/m)`.**

i.e. **the period sequence `(η_c)_c` is the inverse DFT of the Gauss-sum sequence `(τ(χ_j))_j`.**
Parseval: `Σ_c|η_c|² = (1/m)Σ_j|τ(χ_j)|² ≈ p`, so `avg_c|η_c|² ≈ p/m = n` (the proven √n average).

The prize δ* (window placement) reduces (5 axiom-clean bricks, in-tree: `WorstPeriodRootBound`,
`MomentSupNormBridge`, `CleanRangeNorm`, `AutocorrelationMax`) to the single sup-norm bound

> **`B(μ_n) = max_{c≠0} |η_c| ≤ C·√(n · log m) = O(√(n log p))`.**

## The novel reframing: this IS a Salem–Zygmund sup-norm

`max_c|η_c|` is the **sup-norm of the trigonometric polynomial** `P(c) = (1/m)Σ_j τ(χ_j) e(jc/m)`
with `m−1` flat-modulus (`√p`) coefficients. For **random** unimodular coefficients, the classical
**Salem–Zygmund inequality** gives `‖P‖_∞ ≍ √(coeff-energy · log(degree)) = √(n log m)` — **exactly
the prize target, with the exact `√log` factor the §R.3 measurement (`max|η|²≈n(ln p+G)`) found.**

So the prize ⟺ **the Gauss-sum coefficient sequence `(τ(χ_j))` is "Salem–Zygmund-generic"**: its DFT
sup-norm behaves like that of random unimodular coefficients. This is a *derandomization* statement,
and the randomness model is supplied by the **proven equidistribution/independence of Gauss sums**
(Katz monodromy; Adv. Math. 2024 = arXiv 2207.12439, independent joint equidistribution of Gauss
sums attached to monomials). The two ingredients meet exactly here.

## Why this is a better-tooled route than the raw high-moment wall

The campaign's wall is bounding **all** even moments `E_r` up to `r≈ln p` (Bourgain–Shkredov).
The Salem–Zygmund / **generic-chaining** route needs **strictly less**: Talagrand's chaining bounds
`E max_c |η_c|` from the **γ₂ functional of the increment metric** `d(c,c')=‖η_c−η_{c'}‖_{ψ₂}` plus
the diameter — i.e. only the **exponential-moment (MGF) / increment geometry**, not every integer
moment. Concretely it suffices to prove the **sub-Gaussian MGF bound**

> **(SG-MGF)**  `(1/m) Σ_c exp( λ·Re(ζ̄ η_c) ) ≤ exp( C n λ² / 2 )`  for all `λ∈ℝ`, unit `ζ∈ℂ`,

which by Chernoff + union bound over the `m` indices gives `max_c|η_c| ≤ √(2Cn log m)` directly. Via
the DFT identity, `(SG-MGF)` factors over `j` exactly when the Gauss-sum phases are **jointly
sub-independent** — the quantitative form of 2207.12439. So the open input is sharpened from
"all moments Gaussian" to "**one exponential-moment bound, = quantitative joint Gauss-sum
independence over `m−1` characters**" — a single inequality on an object (Gauss sums) with a mature
equidistribution theory (Deligne/Katz), and a chaining apparatus that localizes it to increment
geometry.

## Refutation attempts (survives)

- **§R.3 Gumbel data:** `max|η_c|²≈n(ln p+G)`, `G≈19` bounded, not growing with `n` or 2-adic depth.
  Salem–Zygmund predicts exactly a Gumbel `√(n log m)` law with a bounded additive constant — the
  data **confirms** the reframing rather than refuting it. (A super-`√log` growth would refute it;
  none observed up to `n≤512`, `p≤250k`.)
- **Salem–Zygmund constant:** the random model gives `‖P‖_∞/√(n log m) → 1` (sharp constant); §R.3's
  irrefutable `C=2` and surviving `C=√e` bracket this — consistent, the deterministic Gauss-sum
  sequence is at most as concentrated as random (`B/B_random ≤ 1` measured), the genericity direction.
- **Parseval lower bound:** `max_c|η_c| ≥ avg = √n` always — consistent with `√(n log m) ≥ √n`. The
  `√log` gap between Parseval (average) and Salem–Zygmund (max) is precisely the content; no collapse.

## Honest self-ranking (prize protocol)

- **Novelty 8/10** — the DFT-of-Gauss-sums = Salem–Zygmund-trig-poly identity for the *prize* sup-norm,
  and the generic-chaining/MGF route, are not in the campaign (which frames it via additive energy /
  raw moments). Brings probability theory (Salem–Zygmund, Talagrand chaining) onto the prize for the
  first time.
- **Insight 9/10** — unifies four threads into one classical object: the period DFT, the proven
  Gauss-sum equidistribution (Katz/2207.12439), the §R.3 Gumbel measurement, and the random-trig-poly
  sup-norm law — and explains *why* the `√log` (not the order) is the open content.
- **Proximity 9/10** — dyadic `n=2^k`, `p≡1(n)`, `m≈p/n`: exact prize regime; the `√(n log p)` target
  is the prize δ* window placement, no toy reduction.
- **Feasibility 6/10** — genuinely better than the raw-moment wall: the target is now **one MGF /
  joint-sub-independence inequality** with the Deligne/Katz toolkit and Talagrand chaining, not an
  all-orders moment bound. Still open (the quantitative uniformity over `m−1` characters at thin
  `n≈p^{0.12}` is the residual), so not ≥9 — but the most tractable closed *route* the campaign has,
  because chaining needs only increment geometry, not every moment.

**Bottom line.** A cross-field reframing that converts the prize's open core from a raw high-moment
Bourgain–Shkredov bound into a **Salem–Zygmund sup-norm / sub-Gaussian-MGF statement about the DFT of
the Gauss-sum sequence**, derandomizable via proven Gauss-sum equidistribution and attackable by
generic chaining. The single open input `(SG-MGF)` contains all remaining open math; everything around
it is the in-tree axiom-clean skeleton. Not a closure — a better-tooled, refutation-surviving route.

Papers (added to `PAPERS_NEEDED.md`): Salem–Zygmund / random trig polynomials; Talagrand generic
chaining (sub-Gaussian suprema, Lemma-8.17-type γ₂ bound); 2207.12439 Gauss-sum independence;
1207.1607 value distribution of incomplete Gauss sums; 2602.01781 distribution of additive energy.
Cross-refs: `WorstPeriodRootBound.lean`, `ShawFlatnessRefuted.lean`,
`deltastar-cyclotomic-lattice-collision-core-2026-06-13.md`, workbench §R.3.
