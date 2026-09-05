/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import scripts.probes.astra_mca_residual_rows

/-!
# Polynomial evaluations underlying the four-generator residual rows

The received values and three candidate polynomials use the same four
coefficients. Their absent-core discrepancies are exactly the residual rows.
This file does not assert an MCA probability or threshold theorem.
-/

set_option autoImplicit false

noncomputable section

namespace AstraMcaEvaluations

open Polynomial AstraMcaPolynomialBasis AstraMcaResidualRows

variable {F : Type*} [Field F] [DecidableEq F]

/-- Evaluation of a four-coordinate row against a coefficient vector. -/
def rowDot (r v : Fin 4 → F) : F :=
  v 0 * r 0 + v 1 * r 1 + v 2 * r 2 + v 3 * r 3

omit [DecidableEq F] in
theorem row_dot_add (r u v : Fin 4 → F) : rowDot r (u + v) = rowDot r u + rowDot r v := by
  simp only [rowDot, Pi.add_apply]
  ring

omit [DecidableEq F] in
theorem row_dot_smul (r v : Fin 4 → F) (c : F) : rowDot r (c • v) = c * rowDot r v := by
  simp only [rowDot, Pi.smul_apply, smul_eq_mul]
  ring

/-- A linear combination of the two basis polynomials and their X multiples. -/
def combine (p q : F[X]) (v : Fin 4 → F) : F[X] :=
  C (v 0) * p + C (v 1) * q + C (v 2) * (X * p) + C (v 3) * (X * q)

omit [DecidableEq F] in
theorem combine_eval (p q : F[X]) (v : Fin 4 → F) (x : F) :
    (combine p q v).eval x = rowDot (rowLift x (p.eval x, q.eval x)) v := by
  simp [combine, rowDot, rowLift]

omit [DecidableEq F] in
theorem combine_degree (p q : F[X]) (v : Fin 4 → F) (D : ℕ)
    (hp : p.natDegree ≤ D) (hq : q.natDegree ≤ D) :
    (combine p q v).natDegree ≤ D + 1 := by
  have hXp : (X * p).natDegree ≤ D + 1 := by
    calc
      _ ≤ X.natDegree + p.natDegree := natDegree_mul_le
      _ ≤ D + 1 := by simp only [natDegree_X]; omega
  have hXq : (X * q).natDegree ≤ D + 1 := by
    calc
      _ ≤ X.natDegree + q.natDegree := natDegree_mul_le
      _ ≤ D + 1 := by simp only [natDegree_X]; omega
  unfold combine
  apply natDegree_add_le_of_degree_le
  · apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · exact (natDegree_C_mul_le _ _).trans (by omega)
      · exact (natDegree_C_mul_le _ _).trans (by omega)
    · exact (natDegree_C_mul_le _ _).trans hXp
  · exact (natDegree_C_mul_le _ _).trans hXq

/-- The three candidate polynomials: zero, the F combination, and the G combination. -/
def ownerPolynomial {A B S : Finset F} {D : ℕ} (basis : PairRegionBasis A B S D)
    (v : Fin 4 → F) (k : Fin 3) : F[X] :=
  if k = 0 then 0 else if k = 1 then combine basis.f₀ basis.f₁ v
  else combine basis.g₀ basis.g₁ v

/-- The received value is the F value on S and zero elsewhere. -/
def received {A B S : Finset F} {D : ℕ} (basis : PairRegionBasis A B S D)
    (v : Fin 4 → F) (x : F) : F :=
  if x ∈ S then (combine basis.f₀ basis.f₁ v).eval x else 0

/-- The joint core on which each owner agrees with every coefficient choice. -/
def coreSet (A B S I : Finset F) (k : Fin 3) : Finset F :=
  if k = 0 then A ∪ B ∪ I else if k = 1 then A ∪ S else B ∪ S

omit [Field F] in
/-- The three core sizes follow directly from the disjoint region partition. -/
theorem core_card (A B S I : Finset F) (k : Fin 3)
    (hAB : Disjoint A B) (hAS : Disjoint A S) (hBS : Disjoint B S)
    (hI : Disjoint (A ∪ B ∪ S) I) :
    (coreSet A B S I k).card =
      if k = 0 then A.card + B.card + I.card
      else if k = 1 then A.card + S.card else B.card + S.card := by
  have hABI : Disjoint (A ∪ B) I := hI.mono_left Finset.subset_union_left
  fin_cases k
  · change (A ∪ B ∪ I).card = A.card + B.card + I.card
    rw [Finset.card_union_of_disjoint hABI, Finset.card_union_of_disjoint hAB]
  · change (A ∪ S).card = A.card + S.card
    exact Finset.card_union_of_disjoint hAS
  · change (B ∪ S).card = B.card + S.card
    exact Finset.card_union_of_disjoint hBS

theorem owner_polynomial_degree {A B S : Finset F} {D : ℕ}
    (basis : PairRegionBasis A B S D) (v : Fin 4 → F) (k : Fin 3) :
    (ownerPolynomial basis v k).natDegree ≤ D + 1 := by
  fin_cases k
  · simp [ownerPolynomial]
  · exact combine_degree _ _ v D basis.degree_f₀ basis.degree_f₁
  · exact combine_degree _ _ v D basis.degree_g₀ basis.degree_g₁

theorem core_agrees {A B S I : Finset F} {D : ℕ}
    (basis : PairRegionBasis A B S D)
    (hAS : Disjoint A S) (hBS : Disjoint B S) (hI : Disjoint (A ∪ B ∪ S) I)
    (v : Fin 4 → F) (k : Fin 3) (x : F) (hx : x ∈ coreSet A B S I k) :
    received basis v x = (ownerPolynomial basis v k).eval x := by
  have hIS : Disjoint I S := (hI.mono_left (Finset.subset_union_right)).symm
  fin_cases k
  · have hnS : x ∉ S := by
      simp [coreSet] at hx
      rcases hx with hx | hx | hx
      · exact fun hs => Finset.disjoint_left.mp hAS hx hs
      · exact fun hs => Finset.disjoint_left.mp hBS hx hs
      · exact fun hs => Finset.disjoint_left.mp hIS hx hs
    simp [received, ownerPolynomial, hnS]
  · simp [coreSet] at hx
    rcases hx with hx | hx
    · have hnS : x ∉ S := fun hs => Finset.disjoint_left.mp hAS hx hs
      obtain ⟨hf₀, hf₁⟩ := basis.f_roots x hx
      simp [received, ownerPolynomial, hnS, combine, hf₀, hf₁]
    · simp [received, ownerPolynomial, hx]
  · simp [coreSet] at hx
    rcases hx with hx | hx
    · have hnS : x ∉ S := fun hs => Finset.disjoint_left.mp hBS hx hs
      obtain ⟨hg₀, hg₁⟩ := basis.g_roots x hx
      simp [received, ownerPolynomial, hnS, combine, hg₀, hg₁]
    · obtain ⟨hfg₀, hfg₁⟩ := basis.agrees x hx
      simp [received, ownerPolynomial, hx, combine, hfg₀, hfg₁]

/-- The row is exactly received minus candidate at its absent-core slot. -/
theorem slot_discrepancy {A B S I : Finset F} {D : ℕ}
    (basis : PairRegionBasis A B S D)
    (hAS : Disjoint A S) (hBS : Disjoint B S) (hI : Disjoint (A ∪ B ∪ S) I)
    (v : Fin 4 → F) (j : Fin 3 × F) (hj : j ∈ slotSet A B S I) :
    received basis v j.2 - (ownerPolynomial basis v j.1).eval j.2 =
      rowDot (slotRow basis j) v := by
  have hIS : Disjoint I S := (hI.mono_left (Finset.subset_union_right)).symm
  have hBIS : Disjoint (B ∪ I) S := Finset.disjoint_union_left.mpr ⟨hBS, hIS⟩
  have hAIS : Disjoint (A ∪ I) S := Finset.disjoint_union_left.mpr ⟨hAS, hIS⟩
  obtain ⟨k, x⟩ := j
  simp only [slotSet, Finset.mem_union, Finset.mem_product, Finset.mem_singleton] at hj
  rcases hj with (⟨rfl, hx⟩ | ⟨rfl, hx⟩) | ⟨rfl, hx⟩
  · simp [received, ownerPolynomial, slotRow, baseRow, combine_eval, hx]
  · have hnS : x ∉ S := fun hs => Finset.disjoint_left.mp hBIS (Finset.mem_union.mpr hx) hs
    simp [received, ownerPolynomial, slotRow, baseRow, combine, rowDot, rowLift, hnS]
    ring
  · have hnS : x ∉ S := fun hs => Finset.disjoint_left.mp hAIS (Finset.mem_union.mpr hx) hs
    simp [received, ownerPolynomial, slotRow, baseRow, combine, rowDot, rowLift, hnS]
    ring

/-- Received values respect the same affine combination as the row coefficients. -/
theorem received_affine {A B S : Finset F} {D : ℕ}
    (basis : PairRegionBasis A B S D) (u0 u1 : Fin 4 → F) (c x : F) :
    received basis (u0 + c • u1) x = received basis u0 x + c * received basis u1 x := by
  by_cases hx : x ∈ S
  · simp [received, hx, combine_eval, row_dot_add, row_dot_smul]
  · simp [received, hx]

/-- The row ratio is an actual scalar at which the received word meets its owner polynomial. -/
theorem slot_cancellation {A B S I : Finset F} {D : ℕ}
    (basis : PairRegionBasis A B S D)
    (hAS : Disjoint A S) (hBS : Disjoint B S) (hI : Disjoint (A ∪ B ∪ S) I)
    (u0 u1 : Fin 4 → F) (j : Fin 3 × F) (hj : j ∈ slotSet A B S I)
    (hdenom : rowDot (slotRow basis j) u1 ≠ 0) :
    let c := -rowDot (slotRow basis j) u0 / rowDot (slotRow basis j) u1
    received basis (u0 + c • u1) j.2 =
      (ownerPolynomial basis (u0 + c • u1) j.1).eval j.2 := by
  dsimp only
  apply sub_eq_zero.mp
  rw [slot_discrepancy basis hAS hBS hI _ j hj, row_dot_add, row_dot_smul]
  field_simp
  ring

/-- A nonzero denominator certifies that the slot is outside its owner's joint core. -/
theorem slot_outside_core {A B S I : Finset F} {D : ℕ}
    (basis : PairRegionBasis A B S D)
    (hAS : Disjoint A S) (hBS : Disjoint B S) (hI : Disjoint (A ∪ B ∪ S) I)
    (u1 : Fin 4 → F) (j : Fin 3 × F) (hj : j ∈ slotSet A B S I)
    (hdenom : rowDot (slotRow basis j) u1 ≠ 0) : j.2 ∉ coreSet A B S I j.1 := by
  intro hc
  apply hdenom
  rw [← slot_discrepancy basis hAS hBS hI u1 j hj,
    core_agrees basis hAS hBS hI u1 j.1 j.2 hc, sub_self]

/-- On a core larger than the degree bound, the extra slot rules out even the second explanation. -/
theorem no_explanation_on_core_insert {A B S I : Finset F} {D : ℕ}
    (basis : PairRegionBasis A B S D)
    (hAS : Disjoint A S) (hBS : Disjoint B S) (hI : Disjoint (A ∪ B ∪ S) I)
    (u1 : Fin 4 → F) (j : Fin 3 × F) (hj : j ∈ slotSet A B S I)
    (hdenom : rowDot (slotRow basis j) u1 ≠ 0)
    (U : Finset F) (hU : U ⊆ coreSet A B S I j.1) (hsize : D + 1 < U.card) :
    ¬ ∃ p : F[X], p.natDegree ≤ D + 1 ∧
      ∀ x ∈ insert j.2 U, p.eval x = received basis u1 x := by
  rintro ⟨p, hp, heval⟩
  have hpeq : p = ownerPolynomial basis u1 j.1 := by
    apply eq_of_natDegree_lt_card_of_eval_eq' p (ownerPolynomial basis u1 j.1) U
    · intro x hx
      exact (heval x (Finset.mem_insert_of_mem hx)).trans
        (core_agrees basis hAS hBS hI u1 j.1 x (hU hx))
    · exact (max_le hp (owner_polynomial_degree basis u1 j.1)).trans_lt hsize
  apply hdenom
  rw [← slot_discrepancy basis hAS hBS hI u1 j hj, ← hpeq,
    heval j.2 (Finset.mem_insert_self _ _), sub_self]

/-- The selected scalar has one extra agreement on precisely the support excluding an explanation. -/
theorem core_insert_witness {A B S I : Finset F} {D : ℕ}
    (basis : PairRegionBasis A B S D)
    (hAS : Disjoint A S) (hBS : Disjoint B S) (hI : Disjoint (A ∪ B ∪ S) I)
    (u0 u1 : Fin 4 → F) (j : Fin 3 × F) (hj : j ∈ slotSet A B S I)
    (hdenom : rowDot (slotRow basis j) u1 ≠ 0)
    (U : Finset F) (hU : U ⊆ coreSet A B S I j.1) (hsize : D + 1 < U.card) :
    let c := -rowDot (slotRow basis j) u0 / rowDot (slotRow basis j) u1
    (insert j.2 U).card = U.card + 1 ∧
      (∀ x ∈ insert j.2 U, received basis u0 x + c * received basis u1 x =
        (ownerPolynomial basis (u0 + c • u1) j.1).eval x) ∧
      ¬ (∃ p : F[X], p.natDegree ≤ D + 1 ∧
        ∀ x ∈ insert j.2 U, p.eval x = received basis u1 x) := by
  dsimp only
  refine ⟨Finset.card_insert_of_notMem ?_, ?_,
    no_explanation_on_core_insert basis hAS hBS hI u1 j hj hdenom U hU hsize⟩
  · exact fun hx => slot_outside_core basis hAS hBS hI u1 j hj hdenom (hU hx)
  · intro x hx
    rw [← received_affine]
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x
      exact slot_cancellation basis hAS hBS hI u0 u1 j hj hdenom
    · exact core_agrees basis hAS hBS hI _ j.1 x (hU hx)

end AstraMcaEvaluations

#print axioms AstraMcaEvaluations.row_dot_add
#print axioms AstraMcaEvaluations.row_dot_smul
#print axioms AstraMcaEvaluations.combine_eval
#print axioms AstraMcaEvaluations.combine_degree
#print axioms AstraMcaEvaluations.core_card
#print axioms AstraMcaEvaluations.owner_polynomial_degree
#print axioms AstraMcaEvaluations.core_agrees
#print axioms AstraMcaEvaluations.slot_discrepancy
#print axioms AstraMcaEvaluations.received_affine
#print axioms AstraMcaEvaluations.slot_cancellation
#print axioms AstraMcaEvaluations.slot_outside_core
#print axioms AstraMcaEvaluations.no_explanation_on_core_insert
#print axioms AstraMcaEvaluations.core_insert_witness
