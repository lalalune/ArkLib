/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G171ShiftedREnergyAutocorrelation

/-!
# G172: fixed-cardinality subset sums inject into tuple-sum fibers

Every `r`-element subset has a canonical enumeration by `Fin r`.  The enumeration preserves its
sum and determines the subset from its range.  Hence the number of `r`-subsets with prescribed sum
is at most the corresponding ordered `r`-tuple fiber.  This is the distinct-mark bridge needed to
feed an all-depth deletion code into G171's shifted `rEnergy` bound.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G172SubsetSumToREnergy

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G171ShiftedREnergyAutocorrelation

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

noncomputable def enumSubset (S : Finset F) (r : ℕ) : Fin r → F :=
  if h : S.card = r then
    fun i => (((Fin.castOrderIso h.symm).toEquiv.trans S.equivFin.symm) i : S)
  else fun _ => 0

theorem enumSubset_mem {S : Finset F} {r : ℕ} (hS : S.card = r) (i : Fin r) :
    enumSubset S r i ∈ S := by
  classical
  simp [enumSubset, hS]

theorem enumSubset_sum {S : Finset F} {r : ℕ} (hS : S.card = r) :
    ∑ i, enumSubset S r i = ∑ x ∈ S, x := by
  classical
  let e : Fin r ≃ S := (Fin.castOrderIso hS.symm).toEquiv.trans S.equivFin.symm
  have hsum := Equiv.sum_comp e (fun x : S => (x : F))
  calc
    (∑ i, enumSubset S r i) = ∑ x ∈ S.attach, (x : F) := by
      simpa [enumSubset, hS, e] using hsum
    _ = ∑ x ∈ S, x := by
      exact Finset.sum_attach S (fun x : F => x)

theorem mem_iff_exists_enumSubset {S : Finset F} {r : ℕ} (hS : S.card = r) (x : F) :
    x ∈ S ↔ ∃ i : Fin r, enumSubset S r i = x := by
  classical
  constructor
  · intro hx
    let y : S := ⟨x, hx⟩
    let e : Fin r ≃ S := (Fin.castOrderIso hS.symm).toEquiv.trans S.equivFin.symm
    refine ⟨e.symm y, ?_⟩
    simp [enumSubset, hS, e, y]
  · rintro ⟨i, rfl⟩
    exact enumSubset_mem hS i

theorem enumSubset_injOn_card (r : ℕ) :
    Set.InjOn (fun S : Finset F => enumSubset S r)
      {S : Finset F | S.card = r} := by
  intro S hS T hT henum
  ext x
  rw [mem_iff_exists_enumSubset hS x, mem_iff_exists_enumSubset hT x]
  change enumSubset S r = enumSubset T r at henum
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [← henum]; exact hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [henum]; exact hi⟩

noncomputable def subsetSumFiber (G : Finset F) (r : ℕ) (t : F) : Finset (Finset F) :=
  (G.powersetCard r).filter fun S => ∑ x ∈ S, x = t

theorem enumSubset_maps_sumFiber {G : Finset F} {r : ℕ} {t : F} {S : Finset F}
    (hS : S ∈ subsetSumFiber G r t) :
    enumSubset S r ∈
      (Fintype.piFinset fun _ : Fin r => G).filter (fun v => ∑ i, v i = t) := by
  classical
  rw [subsetSumFiber, Finset.mem_filter, Finset.mem_powersetCard] at hS
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun i => hS.1.1 (enumSubset_mem hS.1.2 i), ?_⟩
  rw [enumSubset_sum hS.1.2, hS.2]

/-- **Distinct-subset fiber bound.** Fixed-cardinality subset sums inject into ordered tuple
sums. -/
theorem subsetSumFiber_card_le_rSumCount (G : Finset F) (r : ℕ) (t : F) :
    (subsetSumFiber G r t).card ≤ rSumCount G r t := by
  classical
  unfold rSumCount
  apply Finset.card_le_card_of_injOn (fun S => enumSubset S r)
  · intro S hS
    exact enumSubset_maps_sumFiber hS
  · intro S hS T hT henum
    apply enumSubset_injOn_card r
    · exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).2
    · exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
    · exact henum

noncomputable def shiftedSubsetSumPairs (G : Finset F) (r : ℕ) (c : F) :
    Finset (Finset F × Finset F) :=
  ((G.powersetCard r ×ˢ G.powersetCard r).filter fun q =>
    (∑ x ∈ q.1, x) = (∑ y ∈ q.2, y) + c)

theorem enumSubsetPair_maps {G : Finset F} {r : ℕ} {c : F} {q : Finset F × Finset F}
    (hq : q ∈ shiftedSubsetSumPairs G r c) :
    (enumSubset q.1 r, enumSubset q.2 r) ∈ shiftedREnergyPairs G r c := by
  classical
  rw [shiftedSubsetSumPairs, Finset.mem_filter, Finset.mem_product] at hq
  rw [shiftedREnergyPairs, Finset.mem_filter, Finset.mem_product,
    Fintype.mem_piFinset, Fintype.mem_piFinset]
  have hL := (Finset.mem_powersetCard.mp hq.1.1)
  have hR := (Finset.mem_powersetCard.mp hq.1.2)
  refine ⟨⟨fun i => hL.1 (enumSubset_mem hL.2 i),
    fun i => hR.1 (enumSubset_mem hR.2 i)⟩, ?_⟩
  rw [enumSubset_sum hL.2, enumSubset_sum hR.2]
  exact hq.2

theorem enumSubsetPair_injOn (G : Finset F) (r : ℕ) (c : F) :
    Set.InjOn (fun q : Finset F × Finset F => (enumSubset q.1 r, enumSubset q.2 r))
      (↑(shiftedSubsetSumPairs G r c) : Set (Finset F × Finset F)) := by
  intro q hq z hz heq
  change q ∈ shiftedSubsetSumPairs G r c at hq
  change z ∈ shiftedSubsetSumPairs G r c at hz
  rw [shiftedSubsetSumPairs, Finset.mem_filter, Finset.mem_product] at hq hz
  apply Prod.ext
  · apply enumSubset_injOn_card r
    · exact (Finset.mem_powersetCard.mp hq.1.1).2
    · exact (Finset.mem_powersetCard.mp hz.1.1).2
    · exact congrArg Prod.fst heq
  · apply enumSubset_injOn_card r
    · exact (Finset.mem_powersetCard.mp hq.1.2).2
    · exact (Finset.mem_powersetCard.mp hz.1.2).2
    · exact congrArg Prod.snd heq

/-- **Shifted distinct-subset capstone.** Pairs of `r`-subsets with prescribed sum difference
inject into the shifted ordered-tuple energy fiber, hence are bounded by `rEnergy`. -/
theorem shiftedSubsetSumPairs_card_le_rEnergy {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (G : Finset K) (r : ℕ) (c : K) :
    (shiftedSubsetSumPairs G r c).card ≤
      ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G r := by
  exact (Finset.card_le_card_of_injOn
    (fun q : Finset K × Finset K => (enumSubset q.1 r, enumSubset q.2 r))
    (fun _ hq => enumSubsetPair_maps hq) (enumSubsetPair_injOn G r c)).trans
      (shiftedREnergyPairs_card_le_rEnergy G r c)

#print axioms enumSubset_sum
#print axioms enumSubset_injOn_card
#print axioms subsetSumFiber_card_le_rSumCount
#print axioms enumSubsetPair_injOn
#print axioms shiftedSubsetSumPairs_card_le_rEnergy

end ArkLib.ProximityGap.Frontier.G172SubsetSumToREnergy
