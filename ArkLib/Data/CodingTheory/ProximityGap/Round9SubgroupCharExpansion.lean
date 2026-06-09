/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

set_option linter.style.longLine false

/-!
# Round 9 (Issue #232, ABF26) — the MULTIPLICATIVE-character expansion of the subgroup indicator:
# the subgroup-restricted mixed Gauss sum decomposed into twisted character Gauss sums.

The prize-deciding scalar `M2 = collisionCount` reduces (via the *additive* Plancherel / spectral
identity of `MomentCollisionSpectral.lean` and `SubsetSumSecondMomentCollision.lean`) to the
**subgroup-restricted partial mixed Gauss sum** `T(b₁,b₂) = ∑_{x∈G} ψ(b₁x + b₂x²)` over the smooth
multiplicative subgroup `G ≤ Fˣ` (`MixedGaussSum*.lean` prove only the *full-field* `‖·‖ = √q` and
flag the subgroup sum as the residual). This file supplies the **inner** decomposition that the
additive spectral layer does not: the multiplicative-character expansion of the *subgroup indicator*.

## Content

For a finite commutative group `M`, the ℂ-valued multiplicative characters form a group of order
`|M|` (`card_mulChar_eq_card`) satisfying the second (dual) orthogonality relation
(`sum_char_eq_ite`):
```
∑_{χ : M̂} χ(a) = |M|·[a = 1].
```
This generalizes Mathlib's `DirichletCharacter.sum_characters_eq` from `(ZMod n)ˣ` to an arbitrary
finite abelian group. Specializing `M = Fˣ ⧸ G` and pulling back along `π : Fˣ → Fˣ ⧸ G` (kernel
exactly `G`) gives the subgroup indicator as the average of the dual characters of the quotient
(`indicator_eq_card_smul_sum_quotChar`):
```
1_{x∈G} = (|G|/|Fˣ|) ∑_{χ : (Fˣ⧸G)^} χ(π x).
```
Masking and exchanging summation yields the keystone (`sum_subgroup_eq_sum_twisted`) and, with
`f(x) = ψ(b₁x + b₂x²)`, the **issue-232 decomposition** (`mixedGaussSum_subgroup_eq_twisted`):
```
∑_{x∈G} ψ(b₁x + b₂x²) = (|G|/(q−1)) ∑_{χ : (Fˣ⧸G)^} ∑_{x∈Fˣ} χ(πx)·ψ(b₁x + b₂x²).
```
The right-hand side ranges over the `[Fˣ:G]` twisted *multiplicative-character* Gauss sums. This is
exactly the decomposition that **isolates** the elementary pieces (`χ` = quadratic character ⇒ Salié
sum, reduced to a quartic + elementary quadratic in `Round9SalieQuarticReduction.lean`) from the
genuinely Weil/RH-for-curves pieces (general `χ`), which Mathlib does not have. It does not close the
prize — it makes the remaining obstruction *precise and machine-checked*.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open scoped BigOperators Classical
open MulChar QuotientGroup

namespace ArkLib.ProximityGap.Round9SubgroupCharExpansion

noncomputable section AbstractDuality

variable {M : Type*} [CommGroup M] [Finite M]

instance : Fintype (MulChar M ℂ) := .ofFinite _

/-- **Second orthogonality, vanishing half.** For a finite commutative group `M` and `a ≠ 1`,
the sum of `χ a` over all ℂ-valued multiplicative characters of `M` vanishes. -/
theorem sum_char_eq_zero_of_ne_one {a : M} (ha : a ≠ 1) :
    ∑ χ : MulChar M ℂ, χ a = 0 := by
  obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity M ℂ ha
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' ↦ rfl

/-- The number of ℂ-valued multiplicative characters of a finite commutative group `M` equals `|M|`. -/
theorem card_mulChar_eq_card : Nat.card (MulChar M ℂ) = Nat.card M := by
  rw [MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity M ℂ]
  exact Nat.card_congr (toUnits (G := M)).toEquiv.symm

/-- **Second orthogonality, full form.** `∑_{χ} χ(a) = |M|` if `a = 1`, else `0`. -/
theorem sum_char_eq_ite (a : M) :
    ∑ χ : MulChar M ℂ, χ a = if a = 1 then (Nat.card M : ℂ) else 0 := by
  split_ifs with ha
  · subst ha
    simp only [map_one, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, card_mulChar_eq_card]
  · exact sum_char_eq_zero_of_ne_one ha

end AbstractDuality

noncomputable section SubgroupIndicator

variable {Fu : Type*} [CommGroup Fu] [Finite Fu] (G : Subgroup Fu)

instance : Fintype (MulChar (Fu ⧸ G) ℂ) := .ofFinite _

/-- **Subgroup indicator via dual characters of the quotient.** `∑_{χ : (Fu⧸G)^} χ(π x)` equals the
index `[Fu:G] = |Fu⧸G|` when `x ∈ G`, and `0` otherwise. -/
theorem sum_quotChar_eq_ite (x : Fu) :
    ∑ χ : MulChar (Fu ⧸ G) ℂ, χ (QuotientGroup.mk x) =
      if x ∈ G then (Nat.card (Fu ⧸ G) : ℂ) else 0 := by
  rw [sum_char_eq_ite (QuotientGroup.mk x), QuotientGroup.eq_one_iff x]

/-- **Subgroup indicator decomposition (division form).** `1_{x∈G} = (1/[Fu:G]) ∑_χ χ(π x)`. -/
theorem indicator_eq_sum_quotChar (x : Fu) :
    (if x ∈ G then (1 : ℂ) else 0) =
      (∑ χ : MulChar (Fu ⧸ G) ℂ, χ (QuotientGroup.mk x)) / (Nat.card (Fu ⧸ G) : ℂ) := by
  rw [sum_quotChar_eq_ite]
  have hpos : (Nat.card (Fu ⧸ G) : ℂ) ≠ 0 := by
    have : 0 < Nat.card (Fu ⧸ G) := Nat.card_pos
    exact_mod_cast this.ne'
  split_ifs with hx
  · field_simp
  · simp

/-- **Subgroup indicator decomposition (coefficient form).** `1_{x∈G} = (|G|/|Fu|) ∑_χ χ(π x)`; the
coefficient is `|G|/(q−1)` when `Fu = Fˣ`. -/
theorem indicator_eq_card_smul_sum_quotChar (x : Fu) :
    (if x ∈ G then (1 : ℂ) else 0) =
      ((Nat.card G : ℂ) / (Nat.card Fu : ℂ)) *
        ∑ χ : MulChar (Fu ⧸ G) ℂ, χ (QuotientGroup.mk x) := by
  have hcard : Nat.card Fu = Nat.card (Fu ⧸ G) * Nat.card G :=
    G.card_eq_card_quotient_mul_card_subgroup
  have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hQ : (Nat.card (Fu ⧸ G) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hcoeff : (Nat.card G : ℂ) / (Nat.card Fu : ℂ) = 1 / (Nat.card (Fu ⧸ G) : ℂ) := by
    rw [hcard]; push_cast; field_simp
  rw [indicator_eq_sum_quotChar, hcoeff, one_div, inv_mul_eq_div]

/-- **Keystone: subgroup-restricted sum decomposed into twisted character sums.** For any
`f : Fu → ℂ`, `∑_{x∈G} f(x) = (|G|/|Fu|) ∑_χ ∑_{x∈Fu} χ(π x) f(x)`. -/
theorem sum_subgroup_eq_sum_twisted [Fintype Fu] (f : Fu → ℂ) :
    ∑ x : Fu, (if x ∈ G then (1 : ℂ) else 0) * f x =
      ((Nat.card G : ℂ) / (Nat.card Fu : ℂ)) *
        ∑ χ : MulChar (Fu ⧸ G) ℂ, ∑ x : Fu, χ (QuotientGroup.mk x) * f x := by
  have key : ∀ x : Fu, (if x ∈ G then (1 : ℂ) else 0) * f x =
      ((Nat.card G : ℂ) / (Nat.card Fu : ℂ)) *
        ∑ χ : MulChar (Fu ⧸ G) ℂ, χ (QuotientGroup.mk x) * f x := by
    intro x
    rw [indicator_eq_card_smul_sum_quotChar, mul_assoc, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun x _ => key x), ← Finset.mul_sum, Finset.sum_comm]

end SubgroupIndicator

/-! ## Concrete instantiation in the issue #232 setting. -/

noncomputable section Issue232

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The smooth multiplicative subgroup: `n`-th roots of unity in `Fˣ`. -/
abbrev G232 (n : ℕ) : Subgroup Fˣ := rootsOfUnity n F

instance (n : ℕ) : Fintype (MulChar (Fˣ ⧸ (G232 (F := F) n)) ℂ) := .ofFinite _

variable (n : ℕ) (ψ : AddChar F ℂ) (b₁ b₂ : F)

/-- **Issue #232: subgroup-restricted mixed Gauss sum = sum of twisted Gauss sums.** With `G` the
`n`-th roots of unity in `Fˣ` and `f(x) = ψ(b₁ x + b₂ x²)`, the subgroup-restricted partial mixed
Gauss sum decomposes as `(|G|/(q−1)) ∑_χ T_χ`, each twisted piece `T_χ = ∑_{x∈Fˣ} χ(π x)·ψ(b₁x+b₂x²)`
ranging over the `[Fˣ:G]` multiplicative characters of `Fˣ⧸G`. The exact Fourier/character
decomposition separating elementary (`χ` quadratic ⇒ Salié) from Weil pieces. -/
theorem mixedGaussSum_subgroup_eq_twisted :
    ∑ x : Fˣ, (if x ∈ (G232 (F := F) n) then (1 : ℂ) else 0) *
        ψ (b₁ * (x : F) + b₂ * (x : F) ^ 2) =
      ((Nat.card (G232 (F := F) n) : ℂ) / (Nat.card Fˣ : ℂ)) *
        ∑ χ : MulChar (Fˣ ⧸ (G232 (F := F) n)) ℂ,
          ∑ x : Fˣ, χ (QuotientGroup.mk x) * ψ (b₁ * (x : F) + b₂ * (x : F) ^ 2) :=
  sum_subgroup_eq_sum_twisted (G232 (F := F) n)
    (fun x => ψ (b₁ * (x : F) + b₂ * (x : F) ^ 2))

end Issue232

end ArkLib.ProximityGap.Round9SubgroupCharExpansion

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round9SubgroupCharExpansion.sum_char_eq_ite
#print axioms ArkLib.ProximityGap.Round9SubgroupCharExpansion.card_mulChar_eq_card
#print axioms ArkLib.ProximityGap.Round9SubgroupCharExpansion.indicator_eq_card_smul_sum_quotChar
#print axioms ArkLib.ProximityGap.Round9SubgroupCharExpansion.sum_subgroup_eq_sum_twisted
#print axioms ArkLib.ProximityGap.Round9SubgroupCharExpansion.mixedGaussSum_subgroup_eq_twisted
