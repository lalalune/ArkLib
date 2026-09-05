/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import scripts.probes.astra_mca_evaluations
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import Mathlib.Data.Finset.Preimage

/-!
# Transporting polynomial supports to the actual MCA event

These theorems use ArkLib's ReedSolomon.code and ProximityGap.mcaEvent
unchanged. The coordinate-domain and support-size assumptions are explicit.
The production support choice, counting, and probability assembly remain separate.
-/

set_option autoImplicit false

noncomputable section

namespace AstraMcaEventBridge

open Polynomial AstraMcaPolynomialBasis AstraMcaResidualRows AstraMcaEvaluations
open scoped NNReal

variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι]

/-- Transport a polynomial same-support witness to the actual indexed RS MCA event. -/
theorem mca_event_from_polynomial_support (dom : ι ↪ F) (d : ℕ) (δ : ℝ≥0)
    (a b : F → F) (c : F) (U : Finset F)
    (hU : ∀ x ∈ U, x ∈ Set.range dom)
    (hsize : (U.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι)
    (p : F[X]) (hp : p.natDegree ≤ d)
    (hagree : ∀ x ∈ U, p.eval x = a x + c * b x)
    (hno : ¬ ∃ q : F[X], q.natDegree ≤ d ∧ ∀ x ∈ U, q.eval x = b x) :
    ProximityGap.mcaEvent (F := F) (ReedSolomon.code dom (d + 1) : Set (ι → F))
      δ (fun i => a (dom i)) (fun i => b (dom i)) c := by
  classical
  letI : NeZero (d + 1) := ⟨by omega⟩
  let S : Finset ι := U.preimage dom dom.injective.injOn
  have hScard : S.card = U.card := by
    dsimp only [S]
    rw [Finset.card_preimage]
    exact congrArg Finset.card (Finset.filter_eq_self.mpr hU)
  refine ⟨S, ?_, ?_, ?_⟩
  · simpa only [hScard] using hsize
  · refine ⟨(fun i => p.eval (dom i)), ?_, ?_⟩
    · refine ⟨p, Polynomial.mem_degreeLT.mpr ?_, rfl⟩
      apply Polynomial.degree_le_natDegree.trans_lt
      exact_mod_cast Nat.lt_succ_of_le hp
    · intro i hi
      simpa only [smul_eq_mul] using hagree (dom i) (Finset.mem_preimage.mp hi)
  · rintro ⟨v0, _, v1, hv1, hjoint⟩
    obtain ⟨q, hq, heq⟩ := hv1
    apply hno
    refine ⟨q, ?_, ?_⟩
    · have hdq := ReedSolomon.natDegree_lt_of_mem_degreeLT hq
      omega
    · intro x hx
      obtain ⟨i, hi⟩ := hU x hx
      have hiS : i ∈ S := Finset.mem_preimage.mpr (hi.symm ▸ hx)
      calc
        q.eval x = q.eval (dom i) := congrArg q.eval hi.symm
        _ = v1 i := congrFun heq i
        _ = b (dom i) := (hjoint i hiS).2
        _ = b x := congrArg b hi

/-- The four-generator support lemma yields ArkLib's actual MCA event. -/
theorem mca_event_of_core_insert (dom : ι ↪ F) (δ : ℝ≥0)
    {A B S I : Finset F} {D : ℕ} (basis : PairRegionBasis A B S D)
    (hAS : Disjoint A S) (hBS : Disjoint B S) (hI : Disjoint (A ∪ B ∪ S) I)
    (u0 u1 : Fin 4 → F) (j : Fin 3 × F) (hj : j ∈ slotSet A B S I)
    (hdenom : rowDot (slotRow basis j) u1 ≠ 0)
    (U : Finset F) (hU : U ⊆ coreSet A B S I j.1) (hlarge : D + 1 < U.card)
    (hrange : ∀ x ∈ insert j.2 U, x ∈ Set.range dom)
    (hsize : ((U.card + 1 : ℕ) : ℝ≥0) ≥ (1 - δ) * Fintype.card ι) :
    ProximityGap.mcaEvent (F := F) (ReedSolomon.code dom (D + 2) : Set (ι → F))
      δ (fun i => received basis u0 (dom i)) (fun i => received basis u1 (dom i))
      (-rowDot (slotRow basis j) u0 / rowDot (slotRow basis j) u1) := by
  obtain ⟨hcount, hagree, hno⟩ :=
    core_insert_witness basis hAS hBS hI u0 u1 j hj hdenom U hU hlarge
  apply mca_event_from_polynomial_support dom (D + 1) δ
    (received basis u0) (received basis u1) _ (insert j.2 U) hrange
    (by simpa only [hcount] using hsize)
    (ownerPolynomial basis
      (u0 + (-rowDot (slotRow basis j) u0 / rowDot (slotRow basis j) u1) • u1) j.1)
    (owner_polynomial_degree basis _ j.1)
  · exact fun x hx => (hagree x hx).symm
  · exact hno

end AstraMcaEventBridge

#print axioms AstraMcaEventBridge.mca_event_from_polynomial_support
#print axioms AstraMcaEventBridge.mca_event_of_core_insert
