/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import scripts.probes.astra_mca_production_basis
import scripts.probes.astra_mca_event_bridge

/-!
# Production supports and actual MCA events

This file applies the polynomial construction and scalar projection to the
certified power domain, using ArkLib's actual ReedSolomon.code and mcaEvent.
The matching universal lower bound remains open.
-/

set_option autoImplicit false

noncomputable section

namespace AstraMcaProductionEvents

open Polynomial AstraMcaPolynomialBasis AstraMcaResidualRows AstraMcaEvaluations
open AstraMcaProductionBasis AstraMcaEventBridge
open ArkLib.ProximityGap.PrizeShapePrimeP30
open scoped NNReal ENNReal

section Regions

variable {F : Type*} [DecidableEq F]

theorem core_subset_domain (A B S I : Finset F) (k : Fin 3) :
    coreSet A B S I k ⊆ A ∪ B ∪ S ∪ I := by
  intro x hx
  fin_cases k <;> simp [coreSet] at hx <;> simp only [Finset.mem_union] <;> aesop

theorem slot_coordinate_mem_domain (A B S I : Finset F)
    (j : Fin 3 × F) (hj : j ∈ slotSet A B S I) : j.2 ∈ A ∪ B ∪ S ∪ I := by
  obtain ⟨k, x⟩ := j
  change x ∈ A ∪ B ∪ S ∪ I
  fin_cases k <;> simp [slotSet] at hj <;> simp only [Finset.mem_union] <;> aesop

end Regions

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩

/-- The actual indexed evaluation domain of the certified generator. -/
def productionEmbedding : Fin (2 ^ 30) ↪ ZMod P where
  toFun i := g ^ (i : ℕ)
  inj' := by
    intro i j h
    apply Fin.ext
    exact pow_injOn_Iio_orderOf
      (Set.mem_Iio.mpr (by rw [orderOf_g]; exact i.isLt))
      (Set.mem_Iio.mpr (by rw [orderOf_g]; exact j.isLt)) h

theorem mem_production_domain_iff (x : ZMod P) :
    x ∈ productionDomain ↔ x ∈ Set.range productionEmbedding := by
  constructor
  · intro hx
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hx
    exact ⟨⟨e, Finset.mem_range.mp he⟩, heq⟩
  · rintro ⟨i, rfl⟩
    exact Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, rfl⟩

/-- The four-deletion upper-bound radius, one Hamming step above the computed bound. -/
def productionRadius : ℝ≥0 := 357913942 / 1073741824

theorem production_support_arithmetic :
    (1 - productionRadius) * Fintype.card (Fin (2 ^ 30)) = (715827882 : ℝ≥0) := by
  apply NNReal.coe_injective
  have hδ : productionRadius ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    norm_num [productionRadius]
  rw [NNReal.coe_mul, NNReal.coe_sub hδ]
  norm_num [productionRadius]

/-- Every slot of the constructed production basis gives an actual bad MCA scalar. -/
theorem production_slot_event {A B S I : Finset (ZMod P)}
    (basis : PairRegionBasis A B S 536870910)
    (hcover : A ∪ B ∪ S ∪ I = productionDomain)
    (hI : Disjoint (A ∪ B ∪ S) I)
    (hAB : Disjoint A B) (hAS : Disjoint A S) (hBS : Disjoint B S)
    (hA : A.card = 357913939) (hB : B.card = 357913939)
    (hS : S.card = 357913942) (hIc : I.card = 4)
    (u0 u1 : Fin 4 → ZMod P) (j : Fin 3 × ZMod P) (hj : j ∈ slotSet A B S I)
    (hdenom : rowDot (slotRow basis j) u1 ≠ 0) :
    ProximityGap.mcaEvent (F := ZMod P)
      (ReedSolomon.code productionEmbedding (2 ^ 29) : Set (Fin (2 ^ 30) → ZMod P))
      productionRadius (fun i => received basis u0 (productionEmbedding i))
      (fun i => received basis u1 (productionEmbedding i))
      (-rowDot (slotRow basis j) u0 / rowDot (slotRow basis j) u1) := by
  have hcore : 715827881 ≤ (coreSet A B S I j.1).card := by
    rw [core_card A B S I j.1 hAB hAS hBS hI, hA, hB, hS, hIc]
    split_ifs <;> decide
  obtain ⟨U, hU, hUcard⟩ := Finset.exists_subset_card_eq hcore
  apply mca_event_of_core_insert productionEmbedding productionRadius basis hAS hBS hI
    u0 u1 j hj hdenom U hU
  · rw [hUcard]
    decide
  · intro x hx
    apply (mem_production_domain_iff x).mp
    rw [← hcover]
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x
      exact slot_coordinate_mem_domain A B S I j hj
    · exact core_subset_domain A B S I j.1 (hU hx)
  · rw [hUcard, production_support_arithmetic]
    norm_num

/-- A single pair of production words admits n+4 distinct actual MCA-bad scalars. -/
theorem production_many_events :
    ∃ u0 u1 : Fin (2 ^ 30) → ZMod P, ∃ bad : Finset (ZMod P),
      bad.card = 1073741828 ∧ ∀ c ∈ bad,
        ProximityGap.mcaEvent (F := ZMod P)
          (ReedSolomon.code productionEmbedding (2 ^ 29) : Set (Fin (2 ^ 30) → ZMod P))
          productionRadius u0 u1 c := by
  classical
  obtain ⟨A, B, S, I, basis, u0, u1, hcover, hI, hAB, hAS, hBS, hA, hB, hS, hIc,
      hcount, hdenom, hinj⟩ := production_scalar_projection
  let scalar := fun j : slotSet A B S I =>
    -rowDot (slotRow basis j.val) u0 / rowDot (slotRow basis j.val) u1
  refine ⟨(fun i => received basis u0 (productionEmbedding i)),
    (fun i => received basis u1 (productionEmbedding i)), Finset.univ.image scalar, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe, hcount]
  · intro c hc
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
    exact production_slot_event basis hcover hI hAB hAS hBS hA hB hS hIc u0 u1
      j.val j.property (hdenom j.val j.property)

end AstraMcaProductionEvents

#print axioms AstraMcaProductionEvents.core_subset_domain
#print axioms AstraMcaProductionEvents.slot_coordinate_mem_domain
#print axioms AstraMcaProductionEvents.mem_production_domain_iff
#print axioms AstraMcaProductionEvents.production_support_arithmetic
#print axioms AstraMcaProductionEvents.production_slot_event
#print axioms AstraMcaProductionEvents.production_many_events
