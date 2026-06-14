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

## SELF-REFUTATION (2026-06-13, same session) — the chaining feasibility boost is FALSE; residual sharpened

Per "refute your own conjecture": I claimed generic chaining beats the moment wall because it needs
only increment geometry. **Refuted by computing the metric.** By Parseval over `c`, the L² increment
is `d̄(c,c')² = (p/m²)·Σ_{j=1}^{m−1} 4sin²(πj(c−c')/m)`. Since `Σ_j sin²(πjδ/m) = (m−1)/2 −
(1/2)Σ_j cos(2πjδ/m) = (m−1)/2 + 1/2 ≈ m/2` for EVERY `δ ≢ 0 (mod m)`, the metric is
**FLAT: `d̄(c,c') ≈ √(2n)` for all distinct pairs.** (The naive small-`δ` Lipschitz estimate
`|1−e(−jδ/m)|≈2πjδ/m` is invalid because `j` runs to `m`, so `jδ` wraps mod `m`.)

For a flat metric on `m` equidistant points, `γ₂ ≈ √(2n)·√(log m)` and **chaining = the union bound**
— there is no multi-scale geometry to exploit. So the route does NOT reduce to "increments only"; it
needs the **per-period sub-Gaussian tail** `P_c(|η_c| ≥ t) ≤ 2exp(−t²/(2C n))`, equivalently the
single-period MGF — which encodes the same even moments `E_r` as the original wall. **Feasibility was
over-credited; revise 6 → 4** (same order as the raw-moment route, no genuine reduction).

**What genuinely survives (the sharpened residual).** The reframing still converts the open core into a
*classical, named* object with a mature literature: the residual is exactly the **sub-Gaussian tail of
the value distribution of the Gaussian period** `η_c` over uniform `c` (a sum `(1/m)Σ_j τ(χ_j)e(−jc/m)`
sampled at a random point) — precisely the **incomplete-Gauss-sum / Gaussian-period value distribution**
studied by Demirci Akarsu–Marklof (arXiv 1207.1607, a proven limit law) and Duke–Garcia (house/value
distribution). The open part is that this limit-law tail is **sub-Gaussian with proxy `O(n)` uniformly
at thin `n≈p^{0.12}`** — a concrete value-distribution-tail statement, not an opaque high-moment bound.
Net: the value-distribution literature (1207.1607 limit law, Duke–Garcia) is the right toolkit, but the
uniform sub-Gaussian tail in the prize regime remains open. Honest scores: novelty 8 / insight 8 /
proximity 9 / **feasibility 4**. Still the cleanest classical *form* of the residual; not a closure.

## DECISIVE LOCALIZATION (2026-06-13) — the prize sits exactly at the edge of Lamzouri's CLT

The sharpened residual ("sub-Gaussian tail of the Gaussian-period value distribution") has a PROVEN
positive answer in an adjacent regime, which pins the open core to an explicit theorem-extension:

**Lamzouri (Distribution of short character sums, arXiv 1106.6072 / Camb. Phil. Soc.):** the value
distribution of a character sum of length `H` converges to a **2-D complex Gaussian** provided
`log H = o(log q)` (with a quantitative Kolmogorov rate). A Gaussian limit ⟹ a **sub-Gaussian tail**
⟹ via the union bound (flat metric, above) `max ≈ √(n log m)` ⟹ **the prize δ* window — in this regime
the prize-true direction is a THEOREM.**

**The boundary IS the prize regime.** Lamzouri needs length `H = q^{o(1)}` (sub-polynomial). The prize
subgroup has `n ≈ p^{1/8}` (e.g. `n=2^32`, `p≈2^256`: `log n/log p = 32/256 = 1/8`), a **fixed power**,
NOT `o(1)`. So the prize is **exactly the first regime where Lamzouri's Gaussian-limit CLT is not
known.** The open core is now the *cleanest possible* statement:

> **(Prize ⟺ Lamzouri-at-fixed-power.)** Extend the 2-D Gaussian value-distribution CLT for the
> subgroup-period sums `η_c` from length `n = p^{o(1)}` to length `n = p^{β}`, `β` a fixed constant
> (`β ≈ 1/8` for the deployed dyadic domain), with variance proxy `O(n)` (uniform sub-Gaussian tail).

This is a recognized hard barrier (the CLT-at-fixed-density is the same Bourgain regime), BUT it is now
"extend a proven theorem by one regime," with a quantitative rate already in hand for `o(log)` — a
concrete, named, attackable target, not an opaque wall. Companion: Lamzouri–Mangerel (large odd-order
character sums, arXiv 1701.01042) bound the MAX `M(χ)≪√q(log q)^{1−δ_g}` for fixed order — the
max-side analogue, also short of the thin-subgroup prize regime. Honest scores for this localization:
novelty 7 / insight 9 / proximity 10 / feasibility 5 (extend-a-CLT is sharper than prove-from-scratch,
still the Bourgain barrier). The prize stays open — but now as "Lamzouri's CLT one regime further."
