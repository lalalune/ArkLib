/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G114DepthThreePopulationNormalForm
import ArkLib.Data.CodingTheory.ProximityGap.SignedPeriodPowerCount

/-!
# G133: nonprincipal Fourier normal form for the fully-disjoint census

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

namespace ArkLib.ProximityGap.Frontier.G133DisjointCensusFourierNormalForm

open Finset
open ArkLib.ProximityGap.SignedPeriodPowerCount
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G96DepthMomentWeld
open ArkLib.ProximityGap.Frontier.G114DepthThreePopulationNormalForm

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The additive-character period of the complement of a word's value support in `G`. -/
noncomputable def complementPeriod
    (ψ : AddChar F ℂ) (G : Finset F) {r : ℕ} (a : Fin r → F) : ℂ :=
  ∑ x ∈ complementOfBag G a, ψ x

/-- The unpunctured additive-character period of `G`. -/
noncomputable def basePeriod (ψ : AddChar F ℂ) (G : Finset F) : ℂ :=
  ∑ x ∈ G, ψ x

/-- The signed change in the `r`-th power caused by puncturing at a word support. -/
noncomputable def punctureCorrection
    (ψ : AddChar F ℂ) (G : Finset F) {r : ℕ} (a : Fin r → F) : ℂ :=
  complementPeriod ψ G a ^ r - basePeriod ψ G ^ r

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

-- The puncture perturbation has norm at most the word length.
omit [Fintype F] in theorem norm_support_character_sum_le
    [Finite F] (ψ : AddChar F ℂ) {r : ℕ} (a : Fin r → F) :
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

-- Every complement period is an `r`-bounded perturbation of the original period.
omit [Fintype F] in theorem norm_complementPeriod_sub_period_le
    [Finite F] (ψ : AddChar F ℂ) (G : Finset F) {r : ℕ} (a : Fin r → F)
    (ha : a ∈ Fintype.piFinset fun _ : Fin r => G) :
    ‖complementPeriod ψ G a - ∑ x ∈ G, ψ x‖ ≤ r := by
  rw [complementPeriod_eq_period_sub_support ψ G a ha]
  simpa only [sub_sub_cancel_left, norm_neg] using norm_support_character_sum_le ψ a

-- Summing the left phase over all words produces the `r`-th power of the negative period.
omit [Fintype F] [DecidableEq F] in theorem sum_leftPhase_eq_negPeriod_pow
    [Finite F] (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) :
    (∑ a ∈ Fintype.piFinset (fun _ : Fin r => G), ψ (-(∑ i, a i))) =
      (∑ x ∈ G, ψ (-x)) ^ r := by
  classical
  letI := Fintype.ofFinite F
  have h := period_pow_eq_tuple_sum G ψ⁻¹ r
  simpa only [AddChar.inv_apply] using h.symm

-- The negative period is the complex conjugate of the original period.
omit [Fintype F] [DecidableEq F] in theorem negPeriod_eq_star_basePeriod
    [Finite F] (ψ : AddChar F ℂ) (G : Finset F) :
    (∑ x ∈ G, ψ (-x)) = (starRingEnd ℂ) (basePeriod ψ G) := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  rw [basePeriod, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [AddChar.starComp_apply hchar, AddChar.inv_apply]

-- Before puncturing, the phase-weighted term is exactly an even absolute moment.
omit [Fintype F] [DecidableEq F] in theorem phase_mul_basePeriod_pow_eq_normSq_pow
    [Finite F] (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) :
    (∑ a ∈ Fintype.piFinset (fun _ : Fin r => G),
        ψ (-(∑ i, a i)) * basePeriod ψ G ^ r) =
      (Complex.normSq (basePeriod ψ G) : ℂ) ^ r := by
  rw [← Finset.sum_mul, sum_leftPhase_eq_negPeriod_pow,
    negPeriod_eq_star_basePeriod, ← mul_pow]
  rw [mul_comm, Complex.mul_conj]

/-- At one fixed left word, the full character sum of the unpunctured term counts all matching-sum
right words. -/
theorem sum_char_phase_mul_basePeriod_pow
    (G : Finset F) {r : ℕ} (a : Fin r → F) :
    (∑ ψ : AddChar F ℂ, ψ (-(∑ i, a i)) * basePeriod ψ G ^ r) =
      (Fintype.card F : ℂ) *
        ((Fintype.piFinset (fun _ : Fin r => G)).filter fun b =>
          ∑ i, b i = ∑ i, a i).card := by
  classical
  have hexp (ψ : AddChar F ℂ) :
      ψ (-(∑ i, a i)) * basePeriod ψ G ^ r =
        ∑ b ∈ Fintype.piFinset (fun _ : Fin r => G),
          ψ (∑ i, b i - ∑ i, a i) := by
    rw [basePeriod, period_pow_eq_tuple_sum G ψ r, Finset.mul_sum]
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

/-- The full additive-character base-period moment is exactly `q * rEnergy`. -/
theorem sum_all_char_normSq_basePeriod_pow_eq_rEnergy
    (G : Finset F) (r : ℕ) :
    (∑ ψ : AddChar F ℂ, (Complex.normSq (basePeriod ψ G) : ℂ) ^ r) =
      (Fintype.card F : ℂ) * rEnergy G r := by
  classical
  rw [Finset.sum_congr rfl fun ψ _ =>
    (phase_mul_basePeriod_pow_eq_normSq_pow ψ G r).symm]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun a _ => sum_char_phase_mul_basePeriod_pow G a]
  rw [← Finset.mul_sum]
  congr 1
  norm_cast
  unfold rEnergy
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : ∑ i, a i = ∑ i, b i
  · rw [if_pos h, if_pos h.symm]
  · have hn : ¬(∑ i, b i = ∑ i, a i) := fun h' => h h'.symm
    rw [if_neg h, if_neg hn]

/-- Removing the principal character gives the centered ordinary `2r`-moment. -/
theorem sum_nonprincipal_normSq_basePeriod_pow_eq_rEnergy
    (G : Finset F) (r : ℕ) :
    (∑ ψ ∈ (Finset.univ.erase (0 : AddChar F ℂ)),
        (Complex.normSq (basePeriod ψ G) : ℂ) ^ r) =
      (Fintype.card F : ℂ) * rEnergy G r - (G.card : ℂ) ^ (2 * r) := by
  classical
  have hsplit := Finset.sum_erase_add (Finset.univ)
    (fun ψ : AddChar F ℂ => (Complex.normSq (basePeriod ψ G) : ℂ) ^ r)
    (Finset.mem_univ (0 : AddChar F ℂ))
  have hzero :
      (Complex.normSq (basePeriod (0 : AddChar F ℂ) G) : ℂ) ^ r =
        (G.card : ℂ) ^ (2 * r) := by
    simp [basePeriod, pow_mul]
    ring
  dsimp only at hsplit
  rw [hzero, sum_all_char_normSq_basePeriod_pow_eq_rEnergy] at hsplit
  exact eq_sub_of_add_eq hsplit

-- Exact split into the ordinary nonprincipal `2r`-moment and the signed puncture correction.
-- `Fintype F` supplies the finite enumeration of all additive characters used in the displayed sum.
set_option linter.unusedFintypeInType false in
theorem complementPeriod_sum_eq_moment_add_punctureCorrection
    (G : Finset F) (r : ℕ) :
    (∑ a ∈ Fintype.piFinset (fun _ : Fin r => G),
      ∑ ψ ∈ (Finset.univ.erase (0 : AddChar F ℂ)),
        ψ (-(∑ i, a i)) * complementPeriod ψ G a ^ r) =
      (∑ ψ ∈ (Finset.univ.erase (0 : AddChar F ℂ)),
          (Complex.normSq (basePeriod ψ G) : ℂ) ^ r) +
        ∑ a ∈ Fintype.piFinset (fun _ : Fin r => G),
          ∑ ψ ∈ (Finset.univ.erase (0 : AddChar F ℂ)),
            ψ (-(∑ i, a i)) * punctureCorrection ψ G a := by
  classical
  have hpoint (a : Fin r → F) (ψ : AddChar F ℂ) :
      ψ (-(∑ i, a i)) * complementPeriod ψ G a ^ r =
        ψ (-(∑ i, a i)) * basePeriod ψ G ^ r +
          ψ (-(∑ i, a i)) * punctureCorrection ψ G a := by
    simp only [punctureCorrection]
    ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ψ _ => phase_mul_basePeriod_pow_eq_normSq_pow ψ G r

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

/-- **G133 headline.** The centered fully-disjoint census is exactly the averaged signed
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

/-- The puncture correction is exactly the difference between the fully-disjoint anomaly and the
ordinary centered `2r`-moment. -/
theorem punctureCorrection_sum_eq_fullDepth_sub_totalAnomaly
    (G : Finset F) (r : ℕ) :
    (∑ a ∈ Fintype.piFinset (fun _ : Fin r => G),
      ∑ ψ ∈ (Finset.univ.erase (0 : AddChar F ℂ)),
        ψ (-(∑ i, a i)) * punctureCorrection ψ G a) =
      ((Fintype.card F : ℂ) * depthFiber G r r - allPairsDepthFiber G r r) -
        ((Fintype.card F : ℂ) * rEnergy G r - (G.card : ℂ) ^ (2 * r)) := by
  calc
    _ = ( ∑ a ∈ Fintype.piFinset (fun _ : Fin r => G),
            ∑ ψ ∈ (Finset.univ.erase (0 : AddChar F ℂ)),
              ψ (-(∑ i, a i)) * complementPeriod ψ G a ^ r) -
          ∑ ψ ∈ (Finset.univ.erase (0 : AddChar F ℂ)),
            (Complex.normSq (basePeriod ψ G) : ℂ) ^ r := by
          rw [complementPeriod_sum_eq_moment_add_punctureCorrection]
          ring
    _ = ((Fintype.card F : ℂ) * depthFiber G r r - allPairsDepthFiber G r r) -
          ∑ ψ ∈ (Finset.univ.erase (0 : AddChar F ℂ)),
            (Complex.normSq (basePeriod ψ G) : ℂ) ^ r := by
          rw [sum_nonprincipal_complementPeriods_eq_fullDepthAnomaly]
    _ = _ := by
          rw [sum_nonprincipal_normSq_basePeriod_pow_eq_rEnergy]

/-- **Fourier/descent duality.** The signed puncture correction is the negative aggregate of every
strictly lower cancellation-depth anomaly. -/
theorem punctureCorrection_sum_eq_neg_lowerDepthAnomalies
    (G : Finset F) (r : ℕ) :
    (∑ a ∈ Fintype.piFinset (fun _ : Fin r => G),
      ∑ ψ ∈ (Finset.univ.erase (0 : AddChar F ℂ)),
        ψ (-(∑ i, a i)) * punctureCorrection ψ G a) =
      -(∑ s ∈ Finset.range r,
        ((Fintype.card F : ℂ) * depthFiber G r s - allPairsDepthFiber G r s)) := by
  rw [punctureCorrection_sum_eq_fullDepth_sub_totalAnomaly,
    rEnergy_eq_sum_depthFiber]
  push_cast
  have hpop :
      (G.card : ℂ) ^ (2 * r) =
        ∑ s ∈ Finset.range (r + 1), (allPairsDepthFiber G r s : ℂ) := by
    norm_cast
    exact (sum_allPairsDepthFiber G r).symm
  rw [hpop]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
  have hsum :
      (Fintype.card F : ℂ) *
          (∑ s ∈ Finset.range r, (depthFiber G r s : ℂ)) -
        ∑ s ∈ Finset.range r, (allPairsDepthFiber G r s : ℂ) =
      ∑ s ∈ Finset.range r,
        ((Fintype.card F : ℂ) * depthFiber G r s - allPairsDepthFiber G r s) := by
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  linear_combination -hsum

#print axioms sum_char_complementPeriod_pow
#print axioms complementPeriod_eq_period_sub_support
#print axioms norm_complementPeriod_sub_period_le
#print axioms phase_mul_basePeriod_pow_eq_normSq_pow
#print axioms complementPeriod_sum_eq_moment_add_punctureCorrection
#print axioms sum_all_char_normSq_basePeriod_pow_eq_rEnergy
#print axioms sum_nonprincipal_normSq_basePeriod_pow_eq_rEnergy
#print axioms punctureCorrection_sum_eq_neg_lowerDepthAnomalies
#print axioms sum_nonprincipal_char_complementPeriod_pow
#print axioms sum_nonprincipal_complementPeriods_eq_conditioned_discrepancy
#print axioms sum_nonprincipal_complementPeriods_eq_fullDepthAnomaly

end ArkLib.ProximityGap.Frontier.G133DisjointCensusFourierNormalForm
