/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import scripts.probes.astra_mca_production_upper

/-!
# The exact single-hole MCA event

For a received direction supported at one coordinate, the actual MCA-bad scalars
are precisely the values at that coordinate of a punctured Reed-Solomon list.
The theorem retains the no-joint condition on the same witness support. It does
not bound that value set or prove the universal production lower bound.
-/

set_option autoImplicit false

noncomputable section

namespace AstraMcaSingleHole

open Polynomial ProximityGap Code
open scoped NNReal ENNReal

variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

/-- A received word with its distinguished coordinate set to zero. -/
def holeBase (a : ι) (v : ι → F) (i : ι) : F := if i = a then 0 else v i

/-- The direction supported at the distinguished coordinate. -/
def holeDirection (a : ι) (i : ι) : F := if i = a then 1 else 0

open Classical in
/-- All agreements outside the distinguished coordinate. -/
def puncturedAgreements (dom : ι ↪ F) (a : ι) (v : ι → F) (f : F[X]) : Finset ι :=
  Finset.univ.filter fun i => i ≠ a ∧ f.eval (dom i) = v i

omit [Fintype ι] [DecidableEq ι] in
/-- The actual RS code has the expected non-strict natural-degree description. -/
theorem codeword_iff_natDegree (dom : ι ↪ F) (d : ℕ) (w : ι → F) :
    w ∈ (ReedSolomon.code dom (d + 1) : Set (ι → F)) ↔
      ∃ f : F[X], f.natDegree ≤ d ∧ ∀ i, f.eval (dom i) = w i := by
  letI : NeZero (d + 1) := ⟨by omega⟩
  constructor
  · rintro ⟨f, hf, heq⟩
    refine ⟨f, ?_, fun i => congrFun heq i⟩
    have hdeg := ReedSolomon.natDegree_lt_of_mem_degreeLT hf
    omega
  · rintro ⟨f, hf, heq⟩
    refine ⟨f, Polynomial.mem_degreeLT.mpr ?_, funext heq⟩
    apply Polynomial.degree_le_natDegree.trans_lt
    exact_mod_cast Nat.lt_succ_of_le hf

omit [Fintype ι] [DecidableEq ι] in
/-- An injective evaluation domain transports the ordinary polynomial root bound. -/
theorem zero_of_indexed_roots (dom : ι ↪ F) (f : F[X]) (S : Finset ι)
    (hzero : ∀ i ∈ S, f.eval (dom i) = 0) (hsize : f.natDegree < S.card) : f = 0 := by
  classical
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' f (S.image dom)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hzero i hi
  · simpa only [Finset.card_image_of_injective S dom.injective] using hsize

omit [Fintype ι] in
/-- A sufficiently large support containing the hole admits no direction codeword. -/
theorem hole_direction_no_explanation (dom : ι ↪ F) (d : ℕ) (a : ι) (S : Finset ι)
    (ha : a ∈ S) (hsize : d + 2 ≤ S.card) :
    ¬ ∃ w ∈ (ReedSolomon.code dom (d + 1) : Set (ι → F)),
      ∀ i ∈ S, w i = holeDirection a i := by
  rintro ⟨w, hw, hagree⟩
  obtain ⟨f, hf, heq⟩ := (codeword_iff_natDegree dom d w).mp hw
  have hzero : f = 0 := by
    apply zero_of_indexed_roots dom f (S.erase a)
    · intro i hi
      simpa only [holeDirection, if_neg (Finset.mem_erase.mp hi).1] using
        (heq i).trans (hagree i (Finset.mem_erase.mp hi).2)
    · rw [Finset.card_erase_of_mem ha]
      omega
  have hone := (heq a).trans (hagree a ha)
  simp [hzero, holeDirection] at hone

/-- The same-support MCA event is exactly the image of the punctured polynomial list. -/
theorem mca_event_iff (dom : ι ↪ F) (d t : ℕ) (δ : ℝ≥0)
    (ht : d + 2 ≤ t) (hthreshold : (1 - δ) * Fintype.card ι = (t : ℝ≥0))
    (a : ι) (v : ι → F) (γ : F) :
    mcaEvent (F := F) (ReedSolomon.code dom (d + 1) : Set (ι → F))
      δ (holeBase a v) (holeDirection a) γ ↔
      ∃ f : F[X], f.natDegree ≤ d ∧ f.eval (dom a) = γ ∧
        t - 1 ≤ (puncturedAgreements dom a v f).card := by
  classical
  constructor
  · rintro ⟨S, hsize, ⟨w, hw, hagree⟩, hno⟩
    have htS : t ≤ S.card := by exact_mod_cast (hthreshold ▸ hsize)
    obtain ⟨f, hf, heq⟩ := (codeword_iff_natDegree dom d w).mp hw
    have ha : a ∈ S := by
      by_contra ha
      apply hno
      refine ⟨w, hw, 0, ?_, ?_⟩
      · exact (codeword_iff_natDegree dom d 0).mpr ⟨0, by simp, by simp⟩
      · intro i hi
        have hia : i ≠ a := fun h => ha (h ▸ hi)
        constructor
        · simpa [holeBase, holeDirection, hia] using hagree i hi
        · simp [holeDirection, hia]
    refine ⟨f, hf, ?_, ?_⟩
    · simpa [holeBase, holeDirection, smul_eq_mul] using (heq a).trans (hagree a ha)
    · have hsub : S.erase a ⊆ puncturedAgreements dom a v f := by
        intro i hi
        obtain ⟨hia, hiS⟩ := Finset.mem_erase.mp hi
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ i, hia, ?_⟩
        simpa [holeBase, holeDirection, hia] using (heq i).trans (hagree i hiS)
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem ha] at hcard
      omega
  · rintro ⟨f, hf, hvalue, hcount⟩
    let U := puncturedAgreements dom a v f
    have haU : a ∉ U := by simp [U, puncturedAgreements]
    have htS : t ≤ (insert a U).card := by
      rw [Finset.card_insert_of_notMem haU]
      dsimp only [U]
      omega
    refine ⟨insert a U, ?_, ?_, ?_⟩
    · rw [hthreshold]
      exact_mod_cast htS
    · refine ⟨fun i => f.eval (dom i), ?_, ?_⟩
      · exact (codeword_iff_natDegree dom d _).mpr ⟨f, hf, fun _ => rfl⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simpa [holeBase, holeDirection, smul_eq_mul] using hvalue
        · obtain ⟨_, hia, hfi⟩ := Finset.mem_filter.mp hi
          simpa [holeBase, holeDirection, hia] using hfi
    · rintro ⟨w0, _, w1, hw1, hjoint⟩
      exact hole_direction_no_explanation dom d a (insert a U)
        (Finset.mem_insert_self a U) (ht.trans htS)
        ⟨w1, hw1, fun i hi => (hjoint i hi).2⟩

section FiniteField

variable [Fintype F]

open Classical in
/-- The value image is finite even though it is described using polynomial witnesses. -/
def valueSet (dom : ι ↪ F) (d t : ℕ) (a : ι) (v : ι → F) : Finset F :=
  Finset.univ.filter fun γ => ∃ f : F[X], f.natDegree ≤ d ∧ f.eval (dom a) = γ ∧
    t - 1 ≤ (puncturedAgreements dom a v f).card

open Classical in
/-- Counting distinct extrapolated values counts the actual bad scalars, without multiplicity. -/
theorem bad_values_card_eq (dom : ι ↪ F) (d t : ℕ) (δ : ℝ≥0)
    (ht : d + 2 ≤ t) (hthreshold : (1 - δ) * Fintype.card ι = (t : ℝ≥0))
    (a : ι) (v : ι → F) :
    (Finset.univ.filter fun γ => mcaEvent (F := F)
      (ReedSolomon.code dom (d + 1) : Set (ι → F)) δ
      (holeBase a v) (holeDirection a) γ).card = (valueSet dom d t a v).card := by
  classical
  congr 1
  ext γ
  simp only [valueSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact mca_event_iff dom d t δ ht hthreshold a v γ

/-- Every value in the punctured image contributes to the original worst-case MCA error. -/
theorem value_count_le_epsMCA [Nonempty ι] (dom : ι ↪ F) (d t : ℕ) (δ : ℝ≥0)
    (ht : d + 2 ≤ t) (hthreshold : (1 - δ) * Fintype.card ι = (t : ℝ≥0))
    (a : ι) (v : ι → F) :
    ((valueSet dom d t a v).card : ℝ≥0∞) / Fintype.card F ≤
      epsMCA (F := F) (ReedSolomon.code dom (d + 1) : Set (ι → F)) δ := by
  classical
  let u : WordStack F (Fin 2) ι := fun j => if j = 0 then holeBase a v else holeDirection a
  apply ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (u := u) (G := valueSet dom d t a v)
  intro γ hγ
  have h := (mca_event_iff dom d t δ ht hthreshold a v γ).mpr
    (Finset.mem_filter.mp hγ).2
  simpa [u] using h

end FiniteField

open AstraMcaProductionEvents AstraMcaProductionUpper
open ArkLib.ProximityGap.PrizeShapePrimeP30

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩

private theorem production_threshold :
    (1 - (357913940 : ℝ≥0) / 1073741824) * Fintype.card (Fin (2 ^ 30)) =
      (715827884 : ℝ≥0) := by
  apply NNReal.coe_injective
  have hδ : (357913940 : ℝ≥0) / 1073741824 ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    norm_num
  rw [NNReal.coe_mul, NNReal.coe_sub hδ]
  norm_num

/-- The exact remaining single-hole value problem at the production predecessor radius. -/
theorem production_single_hole_iff (a : Fin (2 ^ 30)) (v : Fin (2 ^ 30) → ZMod P)
    (γ : ZMod P) :
    mcaEvent (F := ZMod P) productionCode ((357913940 : ℝ≥0) / 1073741824)
      (holeBase a v) (holeDirection a) γ ↔
      ∃ f : Polynomial (ZMod P), f.natDegree ≤ 536870911 ∧
        f.eval (productionEmbedding a) = γ ∧
        715827883 ≤ (puncturedAgreements productionEmbedding a v f).card := by
  exact mca_event_iff productionEmbedding 536870911 715827884 _
    (by norm_num) production_threshold a v γ

/-- The proposed security bound necessarily caps this value image for every punctured word. -/
theorem production_value_budget_of_security
    (hsecurity : epsMCA (F := ZMod P) productionCode
      ((357913940 : ℝ≥0) / 1073741824) ≤ (1 : ℝ≥0∞) / 2 ^ 128)
    (a : Fin (2 ^ 30)) (v : Fin (2 ^ 30) → ZMod P) :
    (valueSet productionEmbedding 536870911 715827884 a v).card ≤ 1073741824 := by
  have hbound :
      ((valueSet productionEmbedding 536870911 715827884 a v).card : ℝ≥0∞) / P ≤
        epsMCA (F := ZMod P) productionCode ((357913940 : ℝ≥0) / 1073741824) := by
    have h := value_count_le_epsMCA productionEmbedding 536870911 715827884
      ((357913940 : ℝ≥0) / 1073741824) (by norm_num) production_threshold a v
    simpa only [ZMod.card] using h
  by_contra hlarge
  have hcard : 1073741825 ≤ (valueSet productionEmbedding 536870911 715827884 a v).card := by
    omega
  have hcast : (1073741825 : ℝ≥0∞) ≤
      (valueSet productionEmbedding 536870911 715827884 a v).card := by
    exact_mod_cast hcard
  have hsmall : (1073741825 : ℝ≥0∞) / P ≤ (1 : ℝ≥0∞) / 2 ^ 128 :=
    ((ENNReal.div_le_div_right hcast _).trans hbound).trans hsecurity
  have hexceeds : (1 : ℝ≥0∞) / 2 ^ 128 < (1073741825 : ℝ≥0∞) / P := by
    apply (ENNReal.toReal_lt_toReal
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
      (ENNReal.div_ne_top (by norm_num) (by norm_num [P]))).mp
    norm_num [ENNReal.toReal_div, ENNReal.toReal_pow, P]
  exact (not_lt_of_ge hsmall) hexceeds

end AstraMcaSingleHole

#print axioms AstraMcaSingleHole.codeword_iff_natDegree
#print axioms AstraMcaSingleHole.zero_of_indexed_roots
#print axioms AstraMcaSingleHole.hole_direction_no_explanation
#print axioms AstraMcaSingleHole.mca_event_iff
#print axioms AstraMcaSingleHole.bad_values_card_eq
#print axioms AstraMcaSingleHole.value_count_le_epsMCA
#print axioms AstraMcaSingleHole.production_single_hole_iff
#print axioms AstraMcaSingleHole.production_value_budget_of_security
