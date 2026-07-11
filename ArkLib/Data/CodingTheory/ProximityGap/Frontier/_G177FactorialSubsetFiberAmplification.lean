/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G176RepetitionDefectCovariance

/-!
# G177: factorial amplification of distinct subset-sum fibers

G172 injected each `r`-subset into one canonical ordered tuple.  In fact every subset contributes
all `r!` permutations of its canonical enumeration, and these ordered tuples are pairwise distinct
across both the subset and permutation coordinates.  Hence

`r! * subsetSumFiber(G,r,t) <= rSumCount(G,r,t)`.

This is the sharp pointwise multiplicity bridge needed for the centered-contraction audit.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G177FactorialSubsetFiberAmplification

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G171ShiftedREnergyAutocorrelation
open ArkLib.ProximityGap.Frontier.G172SubsetSumToREnergy

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

theorem enumSubset_injective {S : Finset F} {r : ℕ} (hS : S.card = r) :
    Function.Injective (enumSubset S r) := by
  classical
  intro i j hij
  unfold enumSubset at hij
  rw [dif_pos hS] at hij
  exact ((Fin.castOrderIso hS.symm).toEquiv.trans S.equivFin.symm).injective
    (Subtype.ext hij)

noncomputable def permutedSubsetFiber (G : Finset F) (r : ℕ) (t : F) :
    Finset (Σ _S : Finset F, Equiv.Perm (Fin r)) :=
  (subsetSumFiber G r t).sigma fun _ => Finset.univ

noncomputable def permutedEnum {r : ℕ}
    (z : Σ _S : Finset F, Equiv.Perm (Fin r)) : Fin r → F :=
  fun i => enumSubset z.1 r (z.2 i)

theorem permutedSubsetFiber_card (G : Finset F) (r : ℕ) (t : F) :
    (permutedSubsetFiber G r t).card = (subsetSumFiber G r t).card * r.factorial := by
  classical
  rw [permutedSubsetFiber, Finset.card_sigma]
  simp [Fintype.card_perm]

theorem permutedEnum_maps {G : Finset F} {r : ℕ} {t : F}
    {z : Σ _S : Finset F, Equiv.Perm (Fin r)} (hz : z ∈ permutedSubsetFiber G r t) :
    permutedEnum z ∈
      (Fintype.piFinset fun _ : Fin r => G).filter (fun v => ∑ i, v i = t) := by
  classical
  rw [permutedSubsetFiber, Finset.mem_sigma] at hz
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  have hS := Finset.mem_filter.mp hz.1
  have hcard := (Finset.mem_powersetCard.mp hS.1).2
  refine ⟨fun i => (Fintype.mem_piFinset.mp (Finset.mem_filter.mp
    (enumSubset_maps_sumFiber hz.1)).1) (z.2 i), ?_⟩
  unfold permutedEnum
  rw [Equiv.sum_comp z.2]
  exact (Finset.mem_filter.mp (enumSubset_maps_sumFiber hz.1)).2

theorem permutedEnum_injOn (G : Finset F) (r : ℕ) (t : F) :
    Set.InjOn permutedEnum
      (↑(permutedSubsetFiber G r t) : Set (Σ _S : Finset F, Equiv.Perm (Fin r))) := by
  intro z hz w hw hfun
  change z ∈ permutedSubsetFiber G r t at hz
  change w ∈ permutedSubsetFiber G r t at hw
  rw [permutedSubsetFiber, Finset.mem_sigma] at hz hw
  have hzcard := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hz.1).1).2
  have hwcard := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hw.1).1).2
  have hS : z.1 = w.1 := by
    ext x
    rw [mem_iff_exists_enumSubset hzcard x, mem_iff_exists_enumSubset hwcard x]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨w.2 (z.2.symm i), ?_⟩
      have heq := congrFun hfun (z.2.symm i)
      unfold permutedEnum at heq
      simpa [hi] using heq.symm
    · rintro ⟨i, hi⟩
      refine ⟨z.2 (w.2.symm i), ?_⟩
      have heq := congrFun hfun (w.2.symm i)
      unfold permutedEnum at heq
      simpa [hi] using heq
  apply Sigma.ext hS
  apply heq_of_eq
  apply Equiv.ext
  intro i
  apply enumSubset_injective hwcard
  have heq := congrFun hfun i
  unfold permutedEnum at heq
  simpa [hS] using heq

/-- **Factorial pointwise amplification.** Every distinct `r`-subset solution supplies all `r!`
ordered tuple solutions. -/
theorem factorial_mul_subsetSumFiber_card_le_rSumCount
    (G : Finset F) (r : ℕ) (t : F) :
    r.factorial * (subsetSumFiber G r t).card ≤ rSumCount G r t := by
  rw [Nat.mul_comm, ← permutedSubsetFiber_card]
  unfold rSumCount
  exact Finset.card_le_card_of_injOn permutedEnum
    (fun _ hz => permutedEnum_maps hz) (permutedEnum_injOn G r t)

#print axioms permutedSubsetFiber_card
#print axioms permutedEnum_injOn
#print axioms factorial_mul_subsetSumFiber_card_le_rSumCount

end ArkLib.ProximityGap.Frontier.G177FactorialSubsetFiberAmplification
