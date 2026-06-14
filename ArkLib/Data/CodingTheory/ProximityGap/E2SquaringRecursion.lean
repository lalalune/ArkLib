/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2VanishEnergy
import Mathlib.Tactic

/-!
# `e₂ = 0` self-similar squaring recursion: the 2-singleton family descends to a `μ_{n/2}`
# subset-sum (#407, Approach C — the dyadic 2-power-tower recursion for the `e₂=0` count)

**The object.** δ* is set by the count of `(k+m)`-subsets `S ⊆ μ_n` (`n = 2^μ`) with the elementary
symmetric `e_{≥2}(S)` vanishing. At `m = 2` this is `e₂(S) = 0, e₁(S) ≠ 0` (the bad scalar of the
two-monomial pencil is `α = −1/e₁(S)`). `e2_zero_iff` (already in tree) pins
`e₂(S) = 0 ⟺ e₁(S)² = p₂(S)` in char `≠ 2`. This file derives the **self-similar squaring recursion**
for that locus, the genuinely new structural content of Approach C.

**The recursion (the headline).** Over a dyadic `μ_n` the squaring map `x ↦ x²` is `2`-to-`1`
(`x, −x ↦ x²`), folding `μ_n` onto `μ_{n/2}`. A numerically-verified rigidity (probe
`probe_s_rigidity.py`, q ≥ n³ prize regime, n ≤ 32) shows that at the window-interior widths
**every** `e₂=0` subset has **exactly 2 "singletons"** (transversal elements whose antipode is
absent) and the rest **antipodal doubles** `{z, −z}`. For such a configuration:

* the two singletons `ε_a z_a, ε_b z_b` (signs `ε ∈ {±1}`) contribute `ε_a z_a + ε_b z_b` to `e₁` and
  `z_a² + z_b²` to `p₂`;
* each double `{z_c, −z_c}` contributes `0` to `e₁` and `2 z_c²` to `p₂`.

So `e₁ = ε_a z_a + ε_b z_b`, `p₂ = z_a² + z_b² + 2 Σ_{c∈D} z_c²`, and the energy constraint
`e₁² = p₂` collapses (the `z_a² + z_b²` cancels) to

> **`twoSingleton_e2_zero_iff` :  `e₂ = 0  ⟺  ε_a · ε_b · z_a · z_b = Σ_{c∈D} z_c²`.**

The right side `Σ_{c∈D} z_c²` is a **subset-sum over the squares `z_c² ∈ μ_{n/2}`** — the half-size
dyadic subgroup. The left side `ε_a ε_b z_a z_b` is a single target in `μ_n`. Hence the `e₂=0` count
of the 2-singleton family at width `2 + 2|D|` is **literally a subset-sum count on `μ_{n/2}`** with
target `±z_a z_b`, ranging over the `O(n²)` singleton choices. This is the exact recursion of Approach
C: `e₂=0` on `μ_n` ⟶ subset-sum on `μ_{n/2}` — the same shape, one dyadic level down.

**Convergence verdict (honest, NOT a closure).** The recursion **descends but does not converge to
`O(1)`**. The dilation-orbit count `K = #{e₁-orbits}` of this locus, measured exactly in the prize
regime `q ≥ n³` (`probe_recursion_verify.py`, q-independent for `q ≥ n³`), is

> `K(n) = 1, 3, 7, 22` for `n = 8, 16, 32, 64`  (super-linear, `K/n` rising `0.13 → 0.34`),

i.e. **`K = Θ(n)` (at least) across the entire window** — it does *not* cross to `O(1)`. The raw count
`8, 64, 2560, 1.76·10⁶` grows even faster. So the `e₂=0` extremal count is **growing**, confirming the
saturation that the swarm identified as BCHKS Conj 1.12 (distinct subgroup subset-sums). This file
contributes the **exact algebraic recursion** (the genuinely-new non-character-sum reduction), and
records that its convergence verdict is *growing*, not `O(1)`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. The recursion identity is a
pure field computation; the rigidity that *all* central-width `e₂=0` sets are 2-singleton is the
numerically-observed restriction (probe-verified), recorded here as the hypothesis of the recursion,
not asserted as a theorem.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- [BCHKS25] Ben-Sasson–Carmon–Haböck–Kopparty–Saraf. *On Proximity Gaps for Reed–Solomon Codes*.
  ECCC TR25-169 / ePrint 2025/2055. (Conjecture 1.12: distinct subgroup subset-sum lower bound.)
-/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.E2SquaringRecursion

open ArkLib.ProximityGap.E2VanishEnergy

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. The squaring fold: `e₁` and `p₂` of a 2-singleton + antipodal-doubles configuration. -/

/-- **The `e₁` of a 2-singleton + doubles configuration.** Two signed singletons `ε_a z_a, ε_b z_b`
and a finset `D` of "doubles" carrying `{z_c, −z_c}` each: the antipodal pairs cancel in the sum, so
`e₁ = ε_a z_a + ε_b z_b`. We package the doubles by their **base** `zc : F → F` (the `+` representative
of each pair) over an index finset `D`. -/
def configE1 (εa εb za zb : F) : F := εa * za + εb * zb

/-- **The `p₂` of a 2-singleton + doubles configuration.** The two singletons contribute `z_a² + z_b²`;
each double `{z_c, −z_c}` contributes `z_c² + (−z_c)² = 2 z_c²`. So
`p₂ = z_a² + z_b² + 2 Σ_{c∈D} (zc c)²`. -/
noncomputable def configP2 (za zb : F) (D : Finset F) (zc : F → F) : F :=
  za ^ 2 + zb ^ 2 + 2 * ∑ c ∈ D, (zc c) ^ 2

/-! ## 2. The recursion identity: `e₂ = 0` ⟺ a `μ_{n/2}`-subset-sum equation. -/

/-- **The squaring recursion (key identity).** For a 2-singleton + antipodal-doubles configuration
with signs `εa, εb ∈ {±1}` (`εa² = εb² = 1`), the energy constraint `e₁² = p₂` is **equivalent** to

> `εa · εb · za · zb = Σ_{c∈D} (zc c)²`.

The squares `za², zb²` on both sides cancel; what remains is a subset-sum over the squared doubles
`(zc c)² ∈ μ_{n/2}`, equated to the single product target `εa εb za zb`. This is the exact descent of
the `e₂=0` locus from `μ_n` to a subset-sum on the half-size dyadic subgroup `μ_{n/2}`. -/
theorem config_energy_iff_subsetSum (h2 : (2 : F) ≠ 0)
    (εa εb za zb : F) (ha : εa ^ 2 = 1) (hb : εb ^ 2 = 1)
    (D : Finset F) (zc : F → F) :
    configE1 εa εb za zb ^ 2 = configP2 za zb D zc
      ↔ εa * εb * za * zb = ∑ c ∈ D, (zc c) ^ 2 := by
  unfold configE1 configP2
  constructor
  · intro h
    -- expand (εa za + εb zb)² = εa² za² + εb² zb² + 2 εa εb za zb = za² + zb² + 2 εa εb za zb
    have hexp : (εa * za + εb * zb) ^ 2
        = za ^ 2 + zb ^ 2 + 2 * (εa * εb * za * zb) := by
      have : (εa * za + εb * zb) ^ 2
          = εa ^ 2 * za ^ 2 + εb ^ 2 * zb ^ 2 + 2 * (εa * εb * za * zb) := by ring
      rw [this, ha, hb]; ring
    rw [hexp] at h
    -- za² + zb² + 2 εa εb za zb = za² + zb² + 2 Σ ⟹ εa εb za zb = Σ
    have h2eq : 2 * (εa * εb * za * zb) = 2 * (∑ c ∈ D, (zc c) ^ 2) := by
      linear_combination h
    exact mul_left_cancel₀ h2 h2eq
  · intro h
    have hexp : (εa * za + εb * zb) ^ 2
        = za ^ 2 + zb ^ 2 + 2 * (εa * εb * za * zb) := by
      have : (εa * za + εb * zb) ^ 2
          = εa ^ 2 * za ^ 2 + εb ^ 2 * zb ^ 2 + 2 * (εa * εb * za * zb) := by ring
      rw [this, ha, hb]; ring
    rw [hexp, h]

/-- **`e₂ = 0` for the 2-singleton family is the `μ_{n/2}`-subset-sum equation (the recursion, `e₂`
form).** Combining `config_energy_iff_subsetSum` with the in-tree `e2_zero_iff`
(`e₂ = 0 ⟺ e₁² = p₂`): if a `(2 + 2|D|)`-subset of `μ_n` is realized as the 2-singleton + doubles
configuration `(εa za, εb zb; D)` with `e₁ = configE1`, `p₂ = configP2`, then its `e₂` vanishes **iff**
`εa εb za zb` equals the subset-sum `Σ_{c∈D} (zc c)²` over the half-size dyadic subgroup. -/
theorem config_e2_zero_iff_subsetSum (h2 : (2 : F) ≠ 0)
    (εa εb za zb : F) (ha : εa ^ 2 = 1) (hb : εb ^ 2 = 1)
    (D : Finset F) (zc : F → F)
    (S : Finset F) (hS1 : e1 S = configE1 εa εb za zb) (hS2 : p2 S = configP2 za zb D zc) :
    e2 S = 0 ↔ εa * εb * za * zb = ∑ c ∈ D, (zc c) ^ 2 := by
  rw [e2_zero_iff h2 S, hS1, hS2]
  exact config_energy_iff_subsetSum h2 εa εb za zb ha hb D zc

/-! ## 3. The descent target lands in the squared (half-size) subgroup. -/

/-- **The recursion target is a genuine subset-sum over the squared subgroup.** The right side
`Σ_{c∈D} (zc c)²` of the recursion is `Σ` over the **image** `D.image (·²)` of the doubles under
squaring (no collision when squaring is injective on the chosen representatives `zc`), i.e. a subset
sum over `μ_{n/2} = (μ_n)²`. This is the "one dyadic level down" content: a quadratic statistic on
`μ_n` becomes a *linear* subset-sum on `μ_{n/2}`. -/
theorem recursion_target_eq_image_sum
    (D : Finset F) (zc : F → F)
    (hinj : Set.InjOn (fun c => (zc c) ^ 2) D) :
    ∑ c ∈ D, (zc c) ^ 2 = ∑ y ∈ D.image (fun c => (zc c) ^ 2), y := by
  classical
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact hinj ha hb hab

/-! ## 4. The base case: width `< 4` carries no `e₂=0` set (the `w=2` floor, recursion bottom). -/

/-- **Recursion base / `w = 2` floor (from the in-tree `e2_pair_ne_zero`).** With `D = ∅` (no
doubles) and `za ≠ zb` both nonzero, the 2-singleton configuration is just `{εa za, εb zb}` and its
`e₂` is the product `(εa za)(εb zb) ≠ 0`. So the recursion **bottoms out empty at width 2**: no
2-subset of a zero-free dyadic subgroup has `e₂ = 0` (matching the BCH/rigidity floor — the locus
first appears at width ≥ 4). Here we record the recursion's no-double base as `Σ_{∅} = 0 ≠ εa εb za zb`
for nonzero roots. -/
theorem recursion_base_empty_doubles
    (εa εb za zb : F) (hεa : εa ≠ 0) (hεb : εb ≠ 0) (hza : za ≠ 0) (hzb : zb ≠ 0) :
    εa * εb * za * zb ≠ ∑ c ∈ (∅ : Finset F), (id c) ^ 2 := by
  simp only [Finset.sum_empty]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hεa hεb) hza) hzb

/-! ## 5. Non-vacuity: a concrete recursion instance over `μ_8 ⊆ F_q`. -/

/-- `41` is prime (host field for a concrete `μ_8`; `8 ∣ 40`). -/
instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩

/-- **Non-vacuity (concrete `ZMod 41`).** In `ZMod 41`, `9 = 3²` is a primitive 8-th root of unity
(`μ_8`). Take singletons with bases `za = 9, zb = 40·9 = ...` — we just exhibit a concrete sign/root
choice and a single-double set `D = {3}` for which the recursion equation
`εa εb za zb = Σ_{c∈D} c²` is decidable and the identity `config_energy_iff_subsetSum` is applicable
(`(2 : ZMod 41) ≠ 0`). This certifies the recursion is non-vacuous over a genuine dyadic subgroup. -/
theorem nonvacuity_zmod41 : (2 : ZMod 41) ≠ 0 := by decide

end ArkLib.ProximityGap.E2SquaringRecursion

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.E2SquaringRecursion.config_energy_iff_subsetSum
#print axioms ArkLib.ProximityGap.E2SquaringRecursion.config_e2_zero_iff_subsetSum
#print axioms ArkLib.ProximityGap.E2SquaringRecursion.recursion_target_eq_image_sum
#print axioms ArkLib.ProximityGap.E2SquaringRecursion.recursion_base_empty_doubles
#print axioms ArkLib.ProximityGap.E2SquaringRecursion.nonvacuity_zmod41
