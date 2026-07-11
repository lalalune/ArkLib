/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G114DepthThreePopulationNormalForm
import ArkLib.Data.CodingTheory.ProximityGap.SignedPeriodPowerCount

/-!
# G130: nonprincipal Fourier normal form for the fully-disjoint census

G126/G128 reduce the production energy wall to a fully-disjoint equal-sum census plus seven top
energies.  G114 conditions that census on the left endpoint.  Here additive-character
orthogonality identifies its centered discrepancy exactly: the principal character is the
unrestricted disjoint population, and every remaining term is a signed complement-period power.

Thus the production `r = 110` census wall is not an unspecified energy estimate: it is precisely
signed cancellation of punctured-subgroup periods, averaged over all left words.

Issue #466.  Exact structural reduction only; no CORE closure claim.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.G130DisjointCensusFourierNormalForm

open Finset
open ArkLib.ProximityGap.SignedPeriodPowerCount
open ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G96DepthMomentWeld
open ArkLib.ProximityGap.Frontier.G114DepthThreePopulationNormalForm

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The additive-character period of the complement of a word's value support in `G`. -/
noncomputable def complementPeriod
    (ψ : AddChar F ℂ) (G : Finset F) {r : ℕ} (a : Fin r → F) : ℂ :=
  ∑ x ∈ complementOfBag G a, ψ x

-- Puncturing by a word support subtracts exactly that support's character sum.
omit [Fintype F] in theorem complementPeriod_eq_period_sub_support
    (ψ : AddChar F ℂ) (G : Finset F) {r : ℕ} (a : Fin r → F)
    (ha : a ∈ Fintype.piFinset fun _ : Fin r => G) :
    complementPeriod ψ G a =
      (∑ x ∈ G, ψ x) - ∑ x ∈ (valueBag a).toFinset, ψ x := by
  have hsupport : (valueBag a).toFinset ⊆ G := by
    intro x hx
    obtain ⟨i, hi⟩ : ∃ i, a i = x := by simpa [valueBag] using hx
    rw [← hi]
    exact Fintype.mem_piFinset.mp ha i
  unfold complementPeriod complementOfBag
  exact eq_sub_of_add_eq (Finset.sum_sdiff hsupport)

/-- The puncture perturbation has norm at most the word length. -/
theorem norm_support_character_sum_le
    (ψ : AddChar F ℂ) {r : ℕ} (a : Fin r → F) :
    ‖∑ x ∈ (valueBag a).toFinset, ψ x‖ ≤ r := by
  calc
    ‖∑ x ∈ (valueBag a).toFinset, ψ x‖ ≤
        ∑ x ∈ (valueBag a).toFinset, ‖ψ x‖ := norm_sum_le _ _
    _ = ((valueBag a).toFinset.card : ℝ) := by
      simp [AddChar.norm_apply]
    _ ≤ r := by
      have h := Multiset.toFinset_card_le (valueBag a)
      have hcard : (valueBag a).card = r := by simp [valueBag]
      rw [hcard] at h
      exact_mod_cast h

/-- Every complement period is an `r`-bounded perturbation of the original period. -/
theorem norm_complementPeriod_sub_period_le
    (ψ : AddChar F ℂ) (G : Finset F) {r : ℕ} (a : Fin r → F)
    (ha : a ∈ Fintype.piFinset fun _ : Fin r => G) :
    ‖complementPeriod ψ G a - ∑ x ∈ G, ψ x‖ ≤ r := by
  rw [complementPeriod_eq_period_sub_support ψ G a ha]
  simpa only [sub_sub_cancel_left, norm_neg] using norm_support_character_sum_le ψ a

/-- Orthogonality at one fixed left endpoint: the full character sum counts exactly the
support-disjoint right endpoints with matching sum. -/
theorem sum_char_complementPeriod_pow
    (G : Finset F) {r : ℕ} (a : Fin r → F) :
    (∑ ψ : AddChar F ℂ,
        ψ (-(∑ i, a i)) * complementPeriod ψ G a ^ r) =
      (Fintype.card F : ℂ) * (disjointEqualSumRightFiber G a).card := by
  classical
  let H := complementOfBag G a
  have hexp (ψ : AddChar F ℂ) :
      ψ (-(∑ i, a i)) * complementPeriod ψ G a ^ r =
        ∑ b ∈ Fintype.piFinset (fun _ : Fin r => H),
          ψ (∑ i, b i - ∑ i, a i) := by
    rw [complementPeriod, period_pow_eq_tuple_sum H ψ r, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [← AddChar.map_add_eq_mul]
    congr 1
    abel
  rw [Finset.sum_congr rfl fun ψ _ => hexp ψ, Finset.sum_comm]
  have hpt (b : Fin r → F) :
      (∑ ψ : AddChar F ℂ, ψ (∑ i, b i - ∑ i, a i)) =
        if (∑ i, b i) = ∑ i, a i then (Fintype.card F : ℂ) else 0 := by
    rw [sum_char_eq_ite]
    congr 1
    simp only [sub_eq_zero]
  rw [Finset.sum_congr rfl fun b _ => hpt b]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 2

/-- Principal-character subtraction at one left endpoint. -/
theorem sum_nonprincipal_char_complementPeriod_pow
    (G : Finset F) {r : ℕ} (a : Fin r → F) :
    (∑ ψ ∈ (Finset.univ.erase (0 : AddChar F ℂ)),
        ψ (-(∑ i, a i)) * complementPeriod ψ G a ^ r) =
      (Fintype.card F : ℂ) * (disjointEqualSumRightFiber G a).card -
        ((complementOfBag G a).card : ℂ) ^ r := by
  classical
  have hsplit := Finset.sum_erase_add (Finset.univ)
    (fun ψ : AddChar F ℂ =>
      ψ (-(∑ i, a i)) * complementPeriod ψ G a ^ r)
    (Finset.mem_univ (0 : AddChar F ℂ))
  have hzero :
      (0 : AddChar F ℂ) (-(∑ i, a i)) * complementPeriod 0 G a ^ r =
        ((complementOfBag G a).card : ℂ) ^ r := by
    simp [complementPeriod]
  dsimp only at hsplit
  rw [hzero, sum_char_complementPeriod_pow] at hsplit
  exact eq_sub_of_add_eq hsplit

/-- Averaged nonprincipal normal form in the G114 conditioned coordinates. -/
theorem sum_nonprincipal_complementPeriods_eq_conditioned_discrepancy
    (G : Finset F) (r : ℕ) :
    (∑ a ∈ Fintype.piFinset (fun _ : Fin r => G),
      ∑ ψ ∈ (Finset.univ.erase (0 : AddChar F ℂ)),
        ψ (-(∑ i, a i)) * complementPeriod ψ G a ^ r) =
      (Fintype.card F : ℂ) *
          (∑ a ∈ Fintype.piFinset (fun _ : Fin r => G),
            (disjointEqualSumRightFiber G a).card : ℕ) -
        (∑ a ∈ Fintype.piFinset (fun _ : Fin r => G),
          (complementOfBag G a).card ^ r : ℕ) := by
  classical
  rw [Finset.sum_congr rfl fun a _ => sum_nonprincipal_char_complementPeriod_pow G a]
  push_cast
  rw [Finset.mul_sum, Finset.sum_sub_distrib]

/-- **G130 headline.** The centered fully-disjoint census is exactly the averaged signed
nonprincipal complement-period sum. -/
theorem sum_nonprincipal_complementPeriods_eq_fullDepthAnomaly
    (G : Finset F) (r : ℕ) :
    (∑ a ∈ Fintype.piFinset (fun _ : Fin r => G),
      ∑ ψ ∈ (Finset.univ.erase (0 : AddChar F ℂ)),
        ψ (-(∑ i, a i)) * complementPeriod ψ G a ^ r) =
      (Fintype.card F : ℂ) * depthFiber G r r - allPairsDepthFiber G r r := by
  rw [sum_nonprincipal_complementPeriods_eq_conditioned_discrepancy,
    depthFiber_full_eq_sum_disjointEqualSumRightFiber,
    allPairsDepthFiber_full_eq_sum_complements]

#print axioms sum_char_complementPeriod_pow
#print axioms complementPeriod_eq_period_sub_support
#print axioms norm_complementPeriod_sub_period_le
#print axioms sum_nonprincipal_char_complementPeriod_pow
#print axioms sum_nonprincipal_complementPeriods_eq_conditioned_discrepancy
#print axioms sum_nonprincipal_complementPeriods_eq_fullDepthAnomaly

end ArkLib.ProximityGap.Frontier.G130DisjointCensusFourierNormalForm
