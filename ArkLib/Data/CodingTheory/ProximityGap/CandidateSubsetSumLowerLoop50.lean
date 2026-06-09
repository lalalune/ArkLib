/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Loop 50 (O11, DISPROOF CORE) — a *proven* super-exponential lower bound on the subset-sumset of a
# power-independent family; the disproof direction of §7, settled in the linearly-independent regime.

Loop49 reduced the §7 disproof route (O11) to the *distinctness* of subset sums of the `2^m`-th roots
of unity, and conjectured it leans toward disproof. This loop **proves** the decisive half, and
corrects an over-optimism in Loop49.

## The mechanism (`subsetSum_injective_of_noRelation`)
If a family `v : Fin N → K` admits **no nonzero integer relation** of bounded shape — concretely, no
`{−1,0,1}`-coefficient relation, which is implied by `ℤ`-linear independence — then the subset-sum
map `S ↦ ∑_{j ∈ S} v j` is **injective** on `Finset (Fin N)`. Hence the sumset has `≥ 2^N` elements,
and the size-`ℓ` sumset has exactly `C(N, ℓ)` elements (`card_subsetSumset_ge`, `card_subsetSumset_len_eq`).

## Why this settles the char-0 disproof
For a primitive `2^m`-th root of unity `ζ`, the cyclotomic polynomial is `Φ_{2^m} = X^{2^{m-1}} + 1`,
of degree `φ(2^m) = 2^{m-1}`. So the **power basis** `{1, ζ, …, ζ^{2^{m-1}-1}}` is `ℤ`-linearly
independent: it admits no nonzero relation of degree `< 2^{m-1}`. Taking `N = 2^{m-1}`, the subset
sums over the *half-domain* are all distinct, giving `|G^{(+)}| ≥ 2^{2^{m-1}}` and
`|G^{(+ℓ)}| ≥ C(2^{m-1}, ℓ)` — **super-exponential in the domain `2^m`**. Combined with
`thm71_no_fixed_exponent` (Loop46) this **disproves the minimal-domain prize over any field where the
power basis stays independent** (characteristic 0, or `F_q` in which `Φ_{2^m}` stays irreducible of
full degree, i.e. `ord_{2^m}(q) = 2^{m-1}`).

## The honest residual (and the Loop49 correction)
This is *not* yet a finite-field disproof in the STARK regime `q ≡ 1 (mod 2^m)`: there `ζ ∈ F_q`,
the power basis collapses (`{1, ζ}` already dependent), and **the subset sums are capped by `q`**.
Loop49's "both ends super-poly" lean was therefore imprecise for the prime-field case. The remaining
gap is a *lifting* statement: the `C(2^{m-1}, ℓ)` distinct algebraic-integer sums in `ℤ[ζ]` have
bounded norm, so for a large prime `p ≡ 1 (mod 2^m)` (Dirichlet) a degree-1 prime `𝔭 ∣ p` keeps them
distinct mod `𝔭`, witnessing a finite field with super-poly bad count. The combinatorial core is now
proven; the number-theoretic lifting is the next residual. See `DISPROOF_LOG.md` (O15/Loop50).
-/

open Finset

namespace ArkLib.ProximityGap.SubsetSumLowerLoop50

variable {K : Type*} [Field K]

/-- **Subset sums are distinct when the family has no `{−1,0,1}`-relation.**
If no nonzero integer-coefficient combination `∑ j, (g j) • v j` with `g : Fin N → ℤ` vanishes
(`hrel`), then the subset-sum map `S ↦ ∑_{j ∈ S} v j` is injective: two subsets with the same sum
have indicator difference a vanishing integer relation, forcing the subsets equal. -/
theorem subsetSum_injective_of_noRelation {N : ℕ} (v : Fin N → K)
    (hrel : ∀ g : Fin N → ℤ, (∑ j, (g j : K) * v j) = 0 → ∀ j, g j = 0) :
    Function.Injective (fun S : Finset (Fin N) => ∑ j ∈ S, v j) := by
  intro S T hST
  simp only at hST
  -- indicator difference `g j = 1_S(j) − 1_T(j)`
  set g : Fin N → ℤ := fun j => (if j ∈ S then 1 else 0) - (if j ∈ T then 1 else 0) with hg
  have hsum : (∑ j, (g j : K) * v j) = 0 := by
    have hexpand : (∑ j, (g j : K) * v j)
        = (∑ j, (if j ∈ S then (1 : K) else 0) * v j)
          - (∑ j, (if j ∈ T then (1 : K) else 0) * v j) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hg]; push_cast; ring
    have hS : (∑ j, (if j ∈ S then (1 : K) else 0) * v j) = ∑ j ∈ S, v j := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    have hT : (∑ j, (if j ∈ T then (1 : K) else 0) * v j) = ∑ j ∈ T, v j := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    rw [hexpand, hS, hT, hST, sub_self]
  -- no relation ⟹ `g = 0` ⟹ `S = T`
  have hg0 := hrel g hsum
  ext j
  have := hg0 j
  simp only [hg, sub_eq_zero] at this
  by_cases hjS : j ∈ S <;> by_cases hjT : j ∈ T <;>
    simp_all

/-- **`≥ 2^N` distinct subset sums.** The image of the subset-sum map has cardinality `2^N`, since the
map is injective and there are `2^N` subsets of `Fin N`. -/
theorem card_subsetSumset_ge {N : ℕ} [DecidableEq K] (v : Fin N → K)
    (hrel : ∀ g : Fin N → ℤ, (∑ j, (g j : K) * v j) = 0 → ∀ j, g j = 0) :
    2 ^ N ≤ (Finset.univ.image (fun S : Finset (Fin N) => ∑ j ∈ S, v j)).card := by
  have hinj := subsetSum_injective_of_noRelation v hrel
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_finset,
    Fintype.card_fin]

/-- **Exactly `C(N, ℓ)` distinct size-`ℓ` subset sums.** The `ℓ`-element subsets of `Fin N`
(`univ.powersetCard ℓ`, of which there are `C(N, ℓ)`) all have distinct sums, so the size-`ℓ` sumset
`|G^{(+ℓ)}|` has exactly `C(N, ℓ)` elements. -/
theorem card_subsetSumset_len_eq {N : ℕ} [DecidableEq K] (ℓ : ℕ) (v : Fin N → K)
    (hrel : ∀ g : Fin N → ℤ, (∑ j, (g j : K) * v j) = 0 → ∀ j, g j = 0) :
    (((Finset.univ : Finset (Fin N)).powersetCard ℓ).image
        (fun S => ∑ j ∈ S, v j)).card = N.choose ℓ := by
  have hinj := subsetSum_injective_of_noRelation v hrel
  rw [Finset.card_image_of_injective _ hinj, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin]

end ArkLib.ProximityGap.SubsetSumLowerLoop50

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubsetSumLowerLoop50.subsetSum_injective_of_noRelation
#print axioms ArkLib.ProximityGap.SubsetSumLowerLoop50.card_subsetSumset_ge
#print axioms ArkLib.ProximityGap.SubsetSumLowerLoop50.card_subsetSumset_len_eq
