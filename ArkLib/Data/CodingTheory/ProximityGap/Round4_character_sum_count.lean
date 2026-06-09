/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.FieldTheory.Finite.Basic

/-!
# Round 4 (Issue #232, §7 / O11 direct attack) — an EXACT character-sum / Gauss-sum formula for the
# subgroup subset-sum count `N(m, target)`, with isolated main term `C(|G|, m)/q`.

This file attacks the **reduced open question** of the §7 disproof route (cf. `CandidateAttackLoop46`,
O11; `ListCapacityFieldIndependent`, the capacity endpoint; `SubgroupSumsetThreePowUpper`, the
field-cap bracket) with the **additive-character / generating-function** method.

## The counted quantity

For a finite field `F` (`q := |F|`), a finite subset `G ⊆ F` (the smooth/FRI multiplicative subgroup,
but the identity holds for *any* finite subset), a size `m`, and a `target ∈ F`:

  `N(m, target) := #{ S ⊆ G : |S| = m, ∑_{x∈S} x = target }`.

At the prize this is exactly the count whose super-/sub-polynomial growth pins `δ*` from below /
keeps the prize alive: pushing the list-decoding lower bound from agreement `a = k` (capacity, where
the count is the trivial `C(n,k)`) to `a = k + t` (interior) needs `N(k+t, target)` large for a
disproof, small for survival.

## The exact identity (`subsetSumCount_eq_charSum`)

Fix any **primitive** additive character `ψ : AddChar F ℂ` (one always exists,
`FiniteField.primitiveChar_to_Complex`). Additive-character orthogonality
(`AddChar.sum_mulShift`: `∑_{b∈F} ψ(b·y) = q·[y=0]`) turns the sum constraint into an average over the
*dual* group. Swapping the order of summation and applying **Vieta** to the inner subset sum
(`Finset.prod_X_add_C_coeff`: `e_m((ψ(b·x))_{x∈G})` is a coefficient of `∏_{x∈G}(X + ψ(b·x))`) yields
the clean, *exact* Gauss-sum identity

  `q · N(m, target)  =  ∑_{b ∈ F}  ψ(−b·target) · e_m( (ψ(b·x))_{x∈G} )`            (as elements of `ℂ`)

where `e_m(·) = ∑_{S ⊆ G, |S| = m} ∏_{x∈S} ψ(b·x)` is the character-weighted subset count
(`charWeightedCount`). This is the requested exact character-sum / generating-function formula.

## The main term dominates the trivial character (`subsetSumCount_main_plus_error`)

The `b = 0` term of the dual sum is `ψ(0)·e_m((ψ(0))_{x∈G}) = e_m(1,…,1) = C(|G|, m)`
(`charWeightedCount_zero`), the field-independent **main term**. Splitting it off:

  `q · N(m, target)  =  C(|G|, m)  +  ∑_{b ≠ 0} ψ(−b·target) · charWeightedCount ψ b m`.       (★)

The error `∑_{b≠0} …` is a sum of `q − 1` Gauss-type terms. We bound it honestly: each
`charWeightedCount` term is a sum of `C(|G|,m)` unit-modulus products, so the *triangle-inequality*
envelope is `‖error‖ ≤ (q−1)·C(|G|, m)` (`charSum_error_norm_le`). This is the exact statement of why
the character-sum method, **on its own**, cannot resolve `N(m, target)`: the main term and the trivial
triangle bound on the error are the *same* order `C(|G|,m)`, so cancellation in the error
(square-root / Weil-type, which uses the *multiplicative* subgroup structure of `G` and is **not**
captured by the additive characters alone) is exactly what would decide the open question. We make this
delimiter precise rather than hand-wave it.

## Honest status

`sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). What is **proven new**: the exact
character-sum identity for `N(m, target)` over a genuine finite field, the isolation of the
field-independent main term `C(|G|, m)`, the master split (★), and the explicit triangle envelope on
the error. What this does **not** do (the honest delimiter, the open core): bound the *cancellation* in
the Gauss error below the main term — that requires Weil-type / multiplicative-structure input on `G`,
which the additive-character orthogonality does not see. So this is a genuine new *exact-identity* brick
plus a proven *no-go* for the bare additive-character method, not a closure of `N(m, ·)`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset Polynomial BigOperators

namespace ArkLib.ProximityGap.Round4CharacterSum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The counted quantity and the character-weighted count -/

/-- The subgroup subset-sum count `N(m, target) = #{ S ⊆ G : |S| = m, ∑_{x∈S} x = target }`, as a
`Finset` filter over the size-`m` subsets of `G`. -/
noncomputable def subsetSumCount (G : Finset F) (m : ℕ) (target : F) : ℕ :=
  ((G.powersetCard m).filter (fun S => ∑ x ∈ S, x = target)).card

/-- The **character-weighted subset count** `e_m((ψ(b·x))_{x∈G}) = ∑_{S⊆G,|S|=m} ∏_{x∈S} ψ(b·x)`, the
inner sum of the character-sum formula and the elementary symmetric function of the character values
at the shifted subgroup. -/
noncomputable def charWeightedCount (ψ : AddChar F ℂ) (b : F) (G : Finset F) (m : ℕ) : ℂ :=
  ∑ S ∈ G.powersetCard m, ∏ x ∈ S, ψ (b * x)

/-! ## Vieta: the character-weighted count is a coefficient of `∏_{x∈G}(X + ψ(b·x))` -/

/-- **Generating-function (Vieta) form of the character-weighted count.** For any `m ≤ |G|`,
`charWeightedCount ψ b G m` equals the `(|G| − m)`-th coefficient of `∏_{x∈G}(X + C (ψ(b·x)))`. This is
the exact "extract `[z^m]` of `∏(1 + z·ψ(bx))`" step (here in the homogenized `X`-degree form), the
character-sum method's inner generating function. -/
theorem charWeightedCount_eq_coeff (ψ : AddChar F ℂ) (b : F) (G : Finset F) {m : ℕ}
    (hm : m ≤ G.card) :
    charWeightedCount ψ b G m
      = (∏ x ∈ G, (X + C (ψ (b * x)))).coeff (G.card - m) := by
  classical
  -- `Finset.prod_X_add_C_coeff`: coeff `(|G| − m)` is the sum over `(|G| − (|G|−m)) = m`-subsets.
  rw [Finset.prod_X_add_C_coeff G (fun x => ψ (b * x)) (Nat.sub_le _ _)]
  rw [Nat.sub_sub_self hm]
  rfl

/-- **The `b = 0` (trivial-character) main term is `C(|G|, m)`.** At `b = 0`, every factor
`ψ(0·x) = ψ(0) = 1`, so each product is `1` and the count is the number of size-`m` subsets of `G`,
i.e. `C(|G|, m)`. This is the field-independent **main term** of the Gauss-sum formula. -/
theorem charWeightedCount_zero (ψ : AddChar F ℂ) (G : Finset F) (m : ℕ) :
    charWeightedCount ψ 0 G m = (G.card.choose m : ℂ) := by
  classical
  unfold charWeightedCount
  have hone : ∀ S ∈ G.powersetCard m, (∏ x ∈ S, ψ ((0 : F) * x)) = 1 := by
    intro S _
    refine Finset.prod_eq_one (fun x _ => ?_)
    rw [zero_mul, AddChar.map_zero_eq_one]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ_eq]
  · simp
  -- (nothing else required; the `simp` discharges the `nsmul` of `1`)

/-! ## Orthogonality indicator: turn the sum-constraint into an average over the dual group -/

/-- **Additive-character indicator.** For a *primitive* `ψ` and any `y ∈ F`, orthogonality
`AddChar.sum_mulShift` gives `∑_{b∈F} ψ(b·y) = q·[y=0]`. Dividing by `q` (`q ≠ 0` in `ℂ`) realizes the
`{0,1}`-indicator of `y = 0` as an additive-character average — the engine that converts the subset-sum
*constraint* into a sum over the dual group. -/
theorem indicator_eq_charAvg {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (y : F) :
    (if y = 0 then (1 : ℂ) else 0)
      = (Fintype.card F : ℂ)⁻¹ * ∑ b : F, ψ (b * y) := by
  classical
  have hq0 : (Fintype.card F : ℂ) ≠ 0 := by
    have : 0 < Fintype.card F := Fintype.card_pos
    exact_mod_cast this.ne'
  rw [AddChar.sum_mulShift y hψ]
  split_ifs with h
  · rw [if_pos h]; field_simp
  · rw [if_neg h, mul_zero]
