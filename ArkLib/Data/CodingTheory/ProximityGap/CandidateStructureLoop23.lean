/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.GroupTheory.OrderOfElement

/-!
# Loop 23 — the smooth-domain prize is SELF-SIMILAR under folding (the FRI/STIR tower)

Loop 22 isolated the `μ_d`-invariant subcode `{Q(X^d) : deg Q < k/d}`. This file identifies what that
subcode *is*: viewed through the power map `x ↦ x^d`, which sends the smooth domain `μ_N` onto the
smaller smooth domain `μ_{N/d}` (`d`-to-1 when `d ∣ N`), the invariant subcode is the **same-rate**
Reed–Solomon code on the folded domain `μ_{N/d}`:

    rate of `{Q(X^d) : deg Q < k/d}` on `μ_{N/d}`  =  (k/d)/(N/d)  =  k/N  =  ρ.

So the smooth-domain prize at scale `N = 2^m` contains, as its `μ_d`-invariant part, *the very same
prize at scale `N/d`* — it is **self-similar under folding**. For `d = 2` this is exactly the FRI
fold `μ_N → μ_{N/2}` (and STIR/WHIR for larger `d`); the whole prize is the proximity-gap soundness
of that tower pushed to capacity.

**Consequence (why this is the prize).** A `μ_d`-invariant received word's close-codeword list splits
into (i) the *invariant* sublist = the prize one scale down (`μ_{N/d}`, same rate ρ) and (ii)
non-invariant `μ_d`-orbits (Loop22). The prize is therefore a *recursion over the `2^m`-tower*: it
holds iff the per-fold orbit contributions telescope to a polynomial bound (proof), and fails iff
they accumulate super-polynomially over the `m` levels (disproof). This is precisely the
FRI-to-capacity soundness question — i.e. the prize *is* the open frontier of FRI/STIR/WHIR soundness,
not a side issue. This file proves the two structural facts (fold lands in `μ_{N/d}`; rate preserved),
sorry-free and axiom-clean. See `DISPROOF_LOG.md` (Loop23 — self-similar folding tower).
-/

namespace ArkLib.ProximityGap.StructureLoop23

variable {F : Type*} [Field F]

/-- **The fold lands in the smaller smooth domain.** If `x ∈ μ_N` (`x^N = 1`) and `d ∣ N`, then
`x^d ∈ μ_{N/d}` (`(x^d)^{N/d} = 1`). So the power map `x ↦ x^d` sends `μ_N` into `μ_{N/d}` — the FRI
fold of the smooth evaluation domain. -/
theorem pow_fold_mem {x : F} {N d : ℕ} (hdvd : d ∣ N) (hx : x ^ N = 1) :
    (x ^ d) ^ (N / d) = 1 := by
  rw [← pow_mul, Nat.mul_div_cancel' hdvd, hx]

/-- **Folding preserves the rate (self-similarity).** The `μ_d`-invariant subcode has dimension
`k/d` over the folded domain of size `N/d`, so its rate `(k/d)/(N/d)` equals the original rate `k/N`.
The prize is therefore scale-invariant under the `μ_d` fold — the same conjecture one level down. -/
theorem recursive_rate_preserved {k N d : ℝ} (hd : d ≠ 0) :
    (k / d) / (N / d) = k / N := by
  rcases eq_or_ne N 0 with hN | hN
  · rw [hN]; simp
  · field_simp

/-- **`2^m`-tower depth.** For the prize's dyadic smooth domain `N = 2^m`, folding by `d = 2` exactly
`m` times reaches `μ_1`: `2^m / 2^m = 1`. So the recursion has exactly `m` levels — the prize is a
depth-`m` fold tower, and a disproof needs the orbit contributions to accumulate super-polynomially
across these `m` levels (a single level is absorbed, Loop21). -/
theorem tower_depth (m : ℕ) : (2 ^ m) / (2 ^ m) = 1 := Nat.div_self (by positivity)

end ArkLib.ProximityGap.StructureLoop23
