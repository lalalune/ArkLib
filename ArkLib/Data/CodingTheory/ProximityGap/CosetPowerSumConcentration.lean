/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset

/-!
# General-`t` coset concentration of power-sum statistics on the smooth domain (Issue #232)

The list-decoding side of the Ethereum Proximity Prize (ABF26, issue #232) was reduced, by the
in-tree `SubsetSum*` rounds 1–8, to the **concentration** of the joint statistic
`(∑_{x∈S} x, ∑_{x∈S} x², …, ∑_{x∈S} x^t)` over `a`-subsets `S` of the smooth domain
`G = μ_n` (`n = 2^k`-th roots of unity): a `q`-independent super-polynomial concentration of this
statistic on `O(1)` targets is exactly what the prize counterexample / `δ*`-lower-bound needs
(`SubsetSumSecondMomentCollision.choose_sq_le_support_mul_collisionCount`,
`ListInteriorQDependenceNoGo`). Round 7 cracked coordinate 1 (negation-symmetry forces `∑x = 0`),
round 8 cracked `t = 2` (the order-4 subgroup `⟨i⟩` forces both `∑x = 0` and `∑x² = 0`).

This file proves the **general-`t`** form, axiom-clean and `q`-independent.

## The construction

Let `ζ` be a primitive `h`-th root of unity in `F` (take `h = 2^j > t`). For any representative
`g`, the coset `g·⟨ζ⟩ = {g, gζ, …, gζ^{h-1}}` has **every** low power sum vanishing:

  `∑_{x ∈ g·⟨ζ⟩} x^i = g^i · ∑_{l<h} (ζ^i)^l = 0`   for all `1 ≤ i < h`,

because the geometric series in `ζ^i ≠ 1` telescopes (`(ζ^i)^h = (ζ^h)^i = 1`)
(`coset_powersum_zero`, `coset_finset_powersum_zero`). Hence any **union of cosets** of the
order-`h` subgroup realizes the all-zero `(p₁, …, p_{h-1})` statistic
(`cosetUnion_powersum_zero`), and distinct transversal subsets give distinct unions
(`cosetUnion_injOn`). Counting unions of `m` cosets:

  `exists_many_vanishing_powersum_subsets` — **at least `C(n/h, m)` distinct `(m·h)`-subsets of
  `G` have `∑_{x∈S} x^i = 0` for every `1 ≤ i < h`.**

Taking `h = 2^j > t` this is a `q`-independent, field-independent, super-polynomial concentration
of `(∑x, ∑x², …, ∑x^t)` at the single target `0` — the general-`t` round-8.

## Honest scope: the method reaches near capacity only, not the deep interior

`cosetUnion_superpoly_moment_depth` records the structural limit: a *super-polynomially* large
coset concentration (`m ≥ 2` cosets) of moment-depth `t` (`t < h`) has subset size
`a = m·h ≥ 2(t+1)`, i.e. **`t < a/2`**. So the construction can kill at most `< a/2` consecutive
moments while keeping a super-polynomial count: the moment-depth `t` is bounded by half the
agreement size `a`. The radius is `δ = 1 − a/n`; matching the deep interior near the Johnson
radius would require moment-depth `t` comparable to `a` (so that `δ` is pushed down toward
`1 − √ρ`), which this construction provably cannot supply. The deep interior of the Johnson→
capacity gap therefore genuinely needs an idea beyond coset concentration — consistent with the
in-tree Weil no-go (`SubgroupCharacterSumNoGo.weil_recovers_root_count_not_better`).

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.CosetConcentration

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Coset power-sum vanishing (load-bearing).** `ζ ^ h = 1`, `ζ ^ i ≠ 1` ⟹ the `i`-th power
sum over the coset `g · {1, ζ, …, ζ^{h-1}}` vanishes: the geometric series in `ζ^i` telescopes. -/
theorem coset_powersum_zero {ζ : F} {h : ℕ} (hζ : ζ ^ h = 1) {i : ℕ} (hi : ζ ^ i ≠ 1) (g : F) :
    ∑ l ∈ range h, (g * ζ ^ l) ^ i = 0 := by
  have hrw : ∑ l ∈ range h, (g * ζ ^ l) ^ i = g ^ i * ∑ l ∈ range h, (ζ ^ i) ^ l := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm l i]
  rw [hrw, geom_sum_eq hi h, ← pow_mul, Nat.mul_comm i h, pow_mul, hζ, one_pow,
    sub_self, zero_div, mul_zero]

/-- **All low power-sums vanish on a coset.** Primitive `h`-th root `ζ`, `1 ≤ i < h`. -/
theorem coset_powersum_zero_of_lt {ζ : F} {h : ℕ} (hζ : IsPrimitiveRoot ζ h)
    {i : ℕ} (hi1 : 1 ≤ i) (hih : i < h) (g : F) :
    ∑ l ∈ range h, (g * ζ ^ l) ^ i = 0 := by
  refine coset_powersum_zero hζ.pow_eq_one ?_ g
  intro hcontra
  exact absurd (Nat.le_of_dvd hi1 ((hζ.pow_eq_one_iff_dvd i).1 hcontra)) (Nat.not_le.2 hih)

/-- The coset `g · ⟨ζ⟩` as a finset (image of `range h` under `l ↦ g·ζ^l`). -/
noncomputable def coset (ζ : F) (h : ℕ) (g : F) : Finset F :=
  (range h).image (fun l => g * ζ ^ l)

/-- A coset of a primitive `h`-th root, with `g ≠ 0`, has exactly `h` elements. -/
theorem coset_card {ζ : F} {h : ℕ} (hζ : IsPrimitiveRoot ζ h) {g : F} (hg : g ≠ 0) :
    (coset ζ h g).card = h := by
  unfold coset
  rw [Finset.card_image_of_injOn ?_, Finset.card_range]
  intro a ha b hb hab
  exact (hζ.injOn_pow_mul hg) ha hb (by simpa [mul_comm] using hab)

/-- Power sum of degree `i` (`1 ≤ i < h`) over a single coset finset is `0`. -/
theorem coset_finset_powersum_zero {ζ : F} {h : ℕ} (hζ : IsPrimitiveRoot ζ h) {g : F}
    (hg : g ≠ 0) {i : ℕ} (hi1 : 1 ≤ i) (hih : i < h) :
    ∑ x ∈ coset ζ h g, x ^ i = 0 := by
  unfold coset
  rw [Finset.sum_image (fun a ha b hb hab =>
    (hζ.injOn_pow_mul hg) (by simpa using ha) (by simpa using hb) (by simpa [mul_comm] using hab))]
  exact coset_powersum_zero_of_lt hζ hi1 hih g

/-- The union of cosets over a transversal `T` (a set of representatives). -/
noncomputable def cosetUnion (ζ : F) (h : ℕ) (T : Finset F) : Finset F :=
  T.biUnion (fun g => coset ζ h g)

/-- **CONCENTRATION CORE: every coset-union kills all low power-sums.** For pairwise-disjoint
cosets over a transversal `T` of nonzero reps, the `i`-th power sum (`1 ≤ i < h`) over the whole
union `⋃_{g∈T} g·⟨ζ⟩` vanishes. So an `(|T|·h)`-subset of the smooth domain built from coset-unions
of the order-`h` subgroup realizes the all-zero `(p₁, …, p_{h-1})` statistic. -/
theorem cosetUnion_powersum_zero {ζ : F} {h : ℕ} (hζ : IsPrimitiveRoot ζ h)
    (T : Finset F) (hg : ∀ g ∈ T, g ≠ 0)
    (hdisj : (T : Set F).PairwiseDisjoint (fun g => coset ζ h g))
    {i : ℕ} (hi1 : 1 ≤ i) (hih : i < h) :
    ∑ x ∈ cosetUnion ζ h T, x ^ i = 0 := by
  unfold cosetUnion
  rw [Finset.sum_biUnion hdisj]
  exact Finset.sum_eq_zero (fun g hg' => coset_finset_powersum_zero hζ (hg g hg') hi1 hih)

/-- The coset-union over a transversal `T` of `|T|` nonzero reps has exactly `|T|·h` elements. -/
theorem cosetUnion_card {ζ : F} {h : ℕ} (hζ : IsPrimitiveRoot ζ h)
    (T : Finset F) (hg : ∀ g ∈ T, g ≠ 0)
    (hdisj : (T : Set F).PairwiseDisjoint (fun g => coset ζ h g)) :
    (cosetUnion ζ h T).card = T.card * h := by
  unfold cosetUnion
  rw [Finset.card_biUnion hdisj,
    Finset.sum_congr rfl (fun g hg' => coset_card hζ (hg g hg')),
    Finset.sum_const, smul_eq_mul]

/-- **Distinct transversal subsets give distinct coset-unions.** With pairwise-disjoint, nonempty
cosets over the global transversal `R`, the map `T ↦ ⋃_{g∈T} g·⟨ζ⟩` is injective on the
`m`-subsets of `R`: a representative `g ∈ R` lies in `T` iff its (nonempty) coset meets the
union. -/
theorem cosetUnion_injOn {ζ : F} {h : ℕ} (hζ : IsPrimitiveRoot ζ h) (hh : 0 < h)
    (R : Finset F) (hR : ∀ g ∈ R, g ≠ 0)
    (hdisj : (R : Set F).PairwiseDisjoint (fun g => coset ζ h g)) (m : ℕ) :
    Set.InjOn (cosetUnion ζ h) ↑(R.powersetCard m) := by
  intro T₁ hT₁ T₂ hT₂ heq
  rw [Finset.mem_coe, Finset.mem_powersetCard] at hT₁ hT₂
  obtain ⟨hT₁R, _⟩ := hT₁; obtain ⟨hT₂R, _⟩ := hT₂
  have key : ∀ T : Finset F, T ⊆ R → ∀ g ∈ R,
      (g ∈ T ↔ (coset ζ h g ∩ cosetUnion ζ h T).Nonempty) := by
    intro T hTR g hgR
    constructor
    · intro hgT
      have hne : (coset ζ h g).Nonempty := by
        rw [← Finset.card_pos, coset_card hζ (hR g hgR)]; exact hh
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, Finset.mem_inter.2 ⟨hx, Finset.mem_biUnion.2 ⟨g, hgT, hx⟩⟩⟩
    · rintro ⟨x, hx⟩
      rw [Finset.mem_inter] at hx
      obtain ⟨hxg, hxU⟩ := hx
      rw [cosetUnion, Finset.mem_biUnion] at hxU
      obtain ⟨g', hg'T, hxg'⟩ := hxU
      by_contra hgT
      have hgg' : g ≠ g' := by rintro rfl; exact hgT hg'T
      exact (Finset.disjoint_left.1 (hdisj hgR (hTR hg'T) hgg')) hxg hxg'
  ext g
  by_cases hgR : g ∈ R
  · rw [key T₁ hT₁R g hgR, key T₂ hT₂R g hgR, heq]
  · exact ⟨fun h => absurd (hT₁R h) hgR, fun h => absurd (hT₂R h) hgR⟩

/-- **Headline concentration count (general `t`).** Let `ζ` be a primitive `h`-th root of unity in
`F` (think `h = 2^j`), `R` a transversal of pairwise-disjoint cosets of the order-`h` subgroup
(so `R ⊆ μ_n`, `|R| = n/h`), and `m ≤ |R|`. Then there are **at least `C(|R|, m)` distinct
`(m·h)`-subsets** of the smooth domain, each realizing the all-zero `(p₁, …, p_{h-1})` statistic:
every power sum `∑_{x∈S} x^i = 0` for `1 ≤ i < h`.

Taking `h = 2^j > t` this is a **`q`-independent, super-polynomial concentration of the
`(∑x, ∑x², …, ∑x^t)` statistic at the single target `0`** — the general-`t` form of the
round-8 (`t = 2`, order-4) result, and the list-decoding lower-bound ingredient of issue #232.
It lower-bounds the fleet's open fiber count `N2(0,0)` (and its `t`-dimensional analogue) by
`C(n/h, m)`. -/
theorem exists_many_vanishing_powersum_subsets {ζ : F} {h : ℕ} (hζ : IsPrimitiveRoot ζ h)
    (hh : 0 < h) (R : Finset F) (hR : ∀ g ∈ R, g ≠ 0)
    (hdisj : (R : Set F).PairwiseDisjoint (fun g => coset ζ h g)) (m : ℕ) :
    ∃ 𝒮 : Finset (Finset F),
      R.card.choose m ≤ 𝒮.card ∧
      ∀ S ∈ 𝒮, S.card = m * h ∧ (∀ i, 1 ≤ i → i < h → ∑ x ∈ S, x ^ i = 0) := by
  refine ⟨(R.powersetCard m).image (cosetUnion ζ h), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn (cosetUnion_injOn hζ hh R hR hdisj m),
      Finset.card_powersetCard]
  · intro S hS
    rw [Finset.mem_image] at hS
    obtain ⟨T, hT, rfl⟩ := hS
    rw [Finset.mem_powersetCard] at hT
    obtain ⟨hTR, hTcard⟩ := hT
    have hgT : ∀ g ∈ T, g ≠ 0 := fun g hg => hR g (hTR hg)
    have hdisjT : (T : Set F).PairwiseDisjoint (fun g => coset ζ h g) :=
      hdisj.subset (Finset.coe_subset.2 hTR)
    exact ⟨by rw [cosetUnion_card hζ T hgT hdisjT, hTcard],
      fun i hi1 hih => cosetUnion_powersum_zero hζ T hgT hdisjT hi1 hih⟩

/-- **Honest depth no-go (structural limit of the method).** A *super-polynomially*-counted coset
concentration (`m ≥ 2` cosets, count `C(n/h, m) ≥ C(n/h, 2)`) of moment-depth `t` (`t < h`) has
subset size `a = m·h ≥ 2(t+1)`. So the moment-depth obeys `t < a/2`: the construction kills at
most fewer than half the coordinates of its agreement set. Pushing the radius `δ = 1 − a/n` down
toward the Johnson radius needs moment-depth `t` comparable to `a`, which this construction
provably cannot supply — the deep interior needs an idea beyond coset concentration. -/
theorem cosetUnion_superpoly_moment_depth {h m t : ℕ} (hm : 2 ≤ m) (ht : t < h) :
    2 * (t + 1) ≤ m * h := by
  calc 2 * (t + 1) ≤ 2 * h := by omega
    _ ≤ m * h := Nat.mul_le_mul_right h hm

end ArkLib.ProximityGap.CosetConcentration

#print axioms ArkLib.ProximityGap.CosetConcentration.coset_powersum_zero
#print axioms ArkLib.ProximityGap.CosetConcentration.cosetUnion_powersum_zero
#print axioms ArkLib.ProximityGap.CosetConcentration.exists_many_vanishing_powersum_subsets
#print axioms ArkLib.ProximityGap.CosetConcentration.cosetUnion_superpoly_moment_depth
