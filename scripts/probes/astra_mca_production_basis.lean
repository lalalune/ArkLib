/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import scripts.probes.astra_mca_residual_rows
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30

/-!
# Polynomial basis over the certified production field and power domain

This file instantiates the root-domain construction with the repository's
certified modulus and generator. It proves the polynomial basis and the
field-size arithmetic used later in the MCA construction. The actual MCA
event, its probability and the threshold theorem remain separate work.
-/

set_option autoImplicit false

namespace AstraMcaProductionBasis

open AstraMcaPolynomialBasis AstraMcaResidualRows
open ArkLib.ProximityGap.PrizeShapePrimeP30

section PowerDomain

variable {F : Type*} [Monoid F] [DecidableEq F]

/-- The finite evaluation domain used by a smooth power-domain code. -/
def powerDomain (g : F) (n : ℕ) : Finset F :=
  (Finset.range n).image fun e => g ^ e

/-- Exact multiplicative order gives the exact number of distinct evaluation points. -/
theorem power_domain_card (g : F) (n : ℕ) (hg : orderOf g = n) :
    (powerDomain g n).card = n := by
  unfold powerDomain
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  exact pow_injOn_Iio_orderOf
    (Set.mem_Iio.mpr (by rw [hg]; exact Finset.mem_range.mp ha))
    (Set.mem_Iio.mpr (by rw [hg]; exact Finset.mem_range.mp hb)) hab

/-- Every evaluation point is an n-th root of unity. -/
theorem power_domain_roots (g : F) (n : ℕ) (hg : orderOf g = n) :
    ∀ x ∈ powerDomain g n, x ^ n = 1 := by
  intro x hx
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hx
  have hgn : g ^ n = 1 := by simpa only [hg] using pow_orderOf_eq_one g
  calc
    (g ^ e) ^ n = (g ^ n) ^ e := by rw [← pow_mul, ← pow_mul, Nat.mul_comm e n]
    _ = 1 := by rw [hgn, one_pow]

end PowerDomain

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩

/-- The concrete domain of the certified production generator. -/
def productionDomain : Finset (ZMod P) := powerDomain g (2 ^ 30)

/-- The complete polynomial basis exists over the actual certified production field. -/
theorem production_deleted_basis :
    ∃ A B S I : Finset (ZMod P), A ∪ B ∪ S ∪ I = productionDomain ∧
      Disjoint (A ∪ B ∪ S) I ∧ Disjoint A B ∧ Disjoint A S ∧ Disjoint B S ∧
      A.card = 357913939 ∧ B.card = 357913939 ∧ S.card = 357913942 ∧ I.card = 4 ∧
      Nonempty (PairRegionBasis A B S 536870910) := by
  apply production_deleted_basis_from_roots productionDomain
  · exact power_domain_card g (2 ^ 30) orderOf_g
  · exact power_domain_roots g (2 ^ 30) orderOf_g

/-- The same constructed basis gives n+4 nonzero, projectively distinct residual rows. -/
theorem production_residual_rows :
    ∃ A B S I : Finset (ZMod P), ∃ basis : PairRegionBasis A B S 536870910,
      A ∪ B ∪ S ∪ I = productionDomain ∧
      Disjoint (A ∪ B ∪ S) I ∧ Disjoint A B ∧ Disjoint A S ∧ Disjoint B S ∧
      A.card = 357913939 ∧ B.card = 357913939 ∧ S.card = 357913942 ∧ I.card = 4 ∧
      (slotSet A B S I).card = 1073741828 ∧
      (∀ j ∈ slotSet A B S I, slotRow basis j ≠ 0) ∧
      (∀ j ∈ slotSet A B S I, ∀ k ∈ slotSet A B S I, ∀ c : ZMod P,
        slotRow basis j = c • slotRow basis k → j = k) := by
  obtain ⟨A, B, S, I, hcover, hI, hAB, hAS, hBS, hA, hB, hS, hIc, ⟨basis⟩⟩ :=
    production_deleted_basis
  refine ⟨A, B, S, I, basis, hcover, hI, hAB, hAS, hBS, hA, hB, hS, hIc, ?_, ?_, ?_⟩
  · rw [slot_count A B S I hI, hA, hB, hS, hIc]
  · exact fun j hj => slot_row_nonzero basis hI j hj
  · exact fun j hj k hk c h => slot_rows_projectively_distinct basis hAB hAS hBS hI j k hj hk c h

/-- The certified field exceeds the projection budget, and n+4 scalars exceed the security budget. -/
theorem production_projection_arithmetic :
    3 * Nat.choose 1073741828 2 < P ∧ P < 1073741828 * 2 ^ 128 := by
  rw [Nat.choose_two_right]
  decide

end AstraMcaProductionBasis

#print axioms AstraMcaProductionBasis.power_domain_card
#print axioms AstraMcaProductionBasis.power_domain_roots
#print axioms AstraMcaProductionBasis.production_deleted_basis
#print axioms AstraMcaProductionBasis.production_residual_rows
#print axioms AstraMcaProductionBasis.production_projection_arithmetic
