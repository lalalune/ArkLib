/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G170TwoDeletionEnergyBound
import ArkLib.ToMathlib.Combinatorics.Additive.HigherEnergy
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# G171: shifted higher energy is bounded by energy at the origin

For `r`-tuples from a finite set `G`, let `R_r(t)` count tuples with sum `t`.  The number of
pairs whose sums differ by `c` is the autocorrelation

`sum_t R_r(t) R_r(t-c)`.

Cauchy--Schwarz and translation invariance show that this is at most
`sum_t R_r(t)^2 = E_r(G)`.  This all-depth statement is the analytic heart needed by an
`r`-mark deletion code.  It is valid in every finite additive group and uses no subgroup or
number-theoretic hypothesis.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G171ShiftedREnergyAutocorrelation

open scoped BigOperators
open ArkLib.ProximityGap.AutocorrelationMax
open ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

noncomputable def rSumCount (G : Finset F) (r : ℕ) (t : F) : ℕ :=
  ((Fintype.piFinset fun _ : Fin r => G).filter fun v => ∑ i, v i = t).card

noncomputable def shiftedREnergyPairs (G : Finset F) (r : ℕ) (c : F) :
    Finset ((Fin r → F) × (Fin r → F)) :=
  (((Fintype.piFinset fun _ : Fin r => G) ×ˢ
      (Fintype.piFinset fun _ : Fin r => G)).filter fun q =>
        ∑ i, q.1 i = (∑ i, q.2 i) + c)

theorem shiftedREnergyPairs_card_eq (G : Finset F) (r : ℕ) (c : F) :
    (shiftedREnergyPairs G r c).card =
      ∑ t : F, rSumCount G r t * rSumCount G r (t - c) := by
  classical
  unfold shiftedREnergyPairs
  rw [Finset.card_filter, Finset.sum_product]
  simp_rw [← Finset.card_filter]
  change (∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
      ((Fintype.piFinset fun _ : Fin r => G).filter fun w =>
        ∑ i, v i = (∑ i, w i) + c).card) = _
  have hmaps : ∀ v ∈ Fintype.piFinset (fun _ : Fin r => G),
      (∑ i, v i) ∈ (Finset.univ : Finset F) := by simp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro t _ht
  calc
    (∑ v ∈ (Fintype.piFinset (fun _ : Fin r => G)).filter (fun v => ∑ i, v i = t),
        ((Fintype.piFinset fun _ : Fin r => G).filter fun w =>
          ∑ i, v i = (∑ i, w i) + c).card) =
        ∑ _v ∈ (Fintype.piFinset (fun _ : Fin r => G)).filter
            (fun v => ∑ i, v i = t), rSumCount G r (t - c) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mem_filter] at hv
      rw [hv.2]
      unfold rSumCount
      congr 1
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hw, heq⟩
        refine ⟨hw, ?_⟩
        rw [eq_sub_iff_add_eq]
        exact heq.symm
      · rintro ⟨hw, heq⟩
        refine ⟨hw, ?_⟩
        rw [heq]
        abel
    _ = rSumCount G r t * rSumCount G r (t - c) := by
      unfold rSumCount
      simp

theorem addREnergy_eq_sum_rSumCount_sq (G : Finset F) (r : ℕ) :
    Finset.addREnergy r G = ∑ t : F, rSumCount G r t ^ 2 := by
  have hzero := shiftedREnergyPairs_card_eq G r 0
  simp only [sub_zero] at hzero
  simp only [pow_two]
  rw [← hzero]
  unfold shiftedREnergyPairs Finset.addREnergy
  congr 1
  ext q
  simp

/-- **All-depth shifted-energy capstone.** The `c`-shifted `r`-sum collision count never exceeds
the ordinary `r`-fold additive energy. -/
theorem shiftedREnergyPairs_card_le_addREnergy (G : Finset F) (r : ℕ) (c : F) :
    (shiftedREnergyPairs G r c).card ≤ Finset.addREnergy r G := by
  rw [shiftedREnergyPairs_card_eq, addREnergy_eq_sum_rSumCount_sq]
  have hauto := autocorr_le_autocorr_zero
    (fun t : F => (rSumCount G r t : ℝ)) (fun _ => by positivity) c
  exact_mod_cast hauto

theorem rEnergy_eq_addREnergy {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (G : Finset K) (r : ℕ) : rEnergy G r = Finset.addREnergy r G := by
  classical
  unfold rEnergy Finset.addREnergy
  rw [Finset.card_filter, Finset.sum_product]

theorem shiftedREnergyPairs_card_le_rEnergy {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (G : Finset K) (r : ℕ) (c : K) :
    (shiftedREnergyPairs G r c).card ≤ rEnergy G r := by
  rw [rEnergy_eq_addREnergy]
  exact shiftedREnergyPairs_card_le_addREnergy G r c

#print axioms shiftedREnergyPairs_card_eq
#print axioms addREnergy_eq_sum_rSumCount_sq
#print axioms shiftedREnergyPairs_card_le_addREnergy
#print axioms rEnergy_eq_addREnergy
#print axioms shiftedREnergyPairs_card_le_rEnergy

end ArkLib.ProximityGap.Frontier.G171ShiftedREnergyAutocorrelation
