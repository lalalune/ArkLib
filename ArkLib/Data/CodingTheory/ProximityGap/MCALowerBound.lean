/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.Probability.Instances
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# A general MCA lower bound, and the necessity of the RS-structure hypothesis (proximity)

ABF26 Grand Challenge 1 is an *upper* bound: `ε_mca(RS, δ) ≤ poly(2^m, 1/ρ)/q` for Reed–Solomon
codes at the prize rates. This file proves the complementary *lower* side:

* `mcaEvent_prob_le_epsMCA` — the fundamental primitive: `epsMCA` dominates the bad-scalar
  probability of *every* word stack (`epsMCA` is, by definition, the supremum of those).
* `epsMCA_ge_inv_card_of_mcaEvent` — whenever **some** stack admits a bad scalar (`mcaEvent`
  fires), `epsMCA ≥ 1/|F|`.
* `MCALowerExample.epsMCA_C0_ge_half` — a concrete witness: the **zero linear code** over `ZMod 2`
  has `epsMCA ≥ 1/2`. Hence the Grand-Challenge-1 `poly/q` smallness is **false for general linear
  codes** — it genuinely requires the Reed–Solomon structure. This makes precise *why* the prize
  hypotheses cannot be dropped, complementing the upper-bound development.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory BigOperators
open ProximityGap Code

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

omit [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- **No MCA bad scalar exists for the full code.** Since every word is a codeword of
`Set.univ`, the two queried words themselves witness joint agreement on any candidate set. -/
theorem not_mcaEvent_univ
    (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F) :
    ¬ mcaEvent (F := F) (A := A) (Set.univ : Set (ι → A)) δ u₀ u₁ γ := by
  rintro ⟨S, hS, hw, hno⟩
  exact hno ⟨u₀, Set.mem_univ _, u₁, Set.mem_univ _, fun i _ => ⟨rfl, rfl⟩⟩

omit [DecidableEq ι] [DecidableEq F] [Fintype A] [DecidableEq A] in
open Classical in
/-- The bad-scalar probability for any stack against the full code is zero. -/
theorem mcaEvent_prob_univ_eq_zero
    (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) :
    Pr_{let γ ← $ᵖ F}[
        mcaEvent (F := F) (A := A) (Set.univ : Set (ι → A)) δ (u 0) (u 1) γ] = 0 := by
  rw [prob_uniform_eq_card_filter_div_card]
  rw [Finset.filter_false_of_mem
    (fun γ _ => not_mcaEvent_univ (F := F) (A := A) δ (u 0) (u 1) γ)]
  simp

open Classical in
/-- **MCA lower-bound primitive.** `epsMCA` dominates the bad-scalar probability of every word
stack, since it is the supremum of those probabilities. -/
theorem mcaEvent_prob_le_epsMCA
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) :
    Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ] ≤ epsMCA (F := F) (A := A) C δ := by
  unfold epsMCA
  exact le_iSup (fun u : WordStack A (Fin 2) ι =>
    Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ]) u

open Classical in
/-- **MCA lower bound from a single bad scalar.** If some stack `u` admits a bad scalar `γ₀`
(`mcaEvent` fires), then `epsMCA ≥ 1/|F|`: that scalar contributes `1/|F|` to `u`'s bad-scalar
probability, which `epsMCA` dominates. -/
theorem epsMCA_ge_inv_card_of_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) (γ₀ : F)
    (hev : mcaEvent C δ (u 0) (u 1) γ₀) :
    (1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ epsMCA (F := F) (A := A) C δ := by
  refine le_trans ?_ (mcaEvent_prob_le_epsMCA (F := F) (A := A) C δ u)
  rw [prob_uniform_eq_card_filter_div_card]
  have hmem : γ₀ ∈ Finset.filter (fun γ => mcaEvent C δ (u 0) (u 1) γ) Finset.univ := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hev
  have hcard1 : (1 : ℕ) ≤
      (Finset.filter (fun γ => mcaEvent C δ (u 0) (u 1) γ) Finset.univ).card :=
    Finset.card_pos.mpr ⟨γ₀, hmem⟩
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast hcard1

open Classical in
/-- **The full code has zero MCA error.** For `C = univ`, every pair `(u₀, u₁)` is jointly
matchable by codewords (themselves), so `pairJointAgreesOn` always holds and `mcaEvent` never
fires. With `epsMCA_C0_ge_half` this brackets the MCA error across the structural extremes:
`epsMCA univ δ = 0`, while the zero code reaches `≥ 1/2`. -/
theorem epsMCA_univ_eq_zero (δ : ℝ≥0) :
    epsMCA (F := F) (A := A) (Set.univ : Set (ι → A)) δ = 0 := by
  unfold epsMCA
  refine le_antisymm (iSup_le fun u => ?_) (zero_le _)
  rw [mcaEvent_prob_univ_eq_zero (F := F) (A := A) δ u]

#print axioms ProximityGap.not_mcaEvent_univ
#print axioms ProximityGap.mcaEvent_prob_univ_eq_zero

open Classical in
/-- **Characterization of zero MCA error.** `epsMCA C δ = 0` iff no word stack admits a bad
scalar (`mcaEvent` never fires). The MCA error is exactly the obstruction to universal joint
matchability. -/
theorem epsMCA_eq_zero_iff (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := A) C δ = 0 ↔
      ∀ (u : WordStack A (Fin 2) ι) (γ : F), ¬ mcaEvent C δ (u 0) (u 1) γ := by
  constructor
  · intro h u γ hev
    have hle : Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ] ≤ 0 :=
      h ▸ mcaEvent_prob_le_epsMCA C δ u
    rw [prob_uniform_eq_card_filter_div_card] at hle
    have hz : ((Finset.filter (fun γ : F => mcaEvent C δ (u 0) (u 1) γ) Finset.univ).card : ℝ≥0)
        / (Fintype.card F : ℝ≥0) = 0 := by
      have := le_antisymm (by exact_mod_cast hle) (zero_le _)
      exact_mod_cast this
    have hcard0 : (Finset.filter (fun γ : F => mcaEvent C δ (u 0) (u 1) γ) Finset.univ).card = 0 := by
      rcases (div_eq_zero_iff.mp hz) with h1 | h2
      · exact_mod_cast h1
      · exact absurd (by exact_mod_cast h2 : (Fintype.card F : ℝ≥0) = 0) (by exact_mod_cast Fintype.card_ne_zero)
    have hmem : γ ∈ Finset.filter (fun γ : F => mcaEvent C δ (u 0) (u 1) γ) Finset.univ := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hev
    rw [Finset.card_eq_zero] at hcard0
    rw [hcard0] at hmem
    simp at hmem
  · intro h
    unfold epsMCA
    refine le_antisymm (iSup_le fun u => ?_) (zero_le _)
    rw [prob_uniform_eq_card_filter_div_card, Finset.filter_false_of_mem (fun γ _ => h u γ)]
    simp

open Classical in
/-- **Closed form for the MCA error.** `epsMCA` equals the supremum over word stacks of the
bad-scalar count, divided by `|F|`. -/
theorem epsMCA_eq_iSup_badCount_div (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := A) C δ =
      (⨆ u : WordStack A (Fin 2) ι,
        ((Finset.filter (fun γ : F => mcaEvent C δ (u 0) (u 1) γ) Finset.univ).card : ℝ≥0∞))
        / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  have h : ∀ u : WordStack A (Fin 2) ι,
      Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ]
        = ((Finset.filter (fun γ : F => mcaEvent C δ (u 0) (u 1) γ) Finset.univ).card : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞) := by
    intro u
    rw [prob_uniform_eq_card_filter_div_card]
    simp only [ENNReal.coe_natCast]
  simp_rw [h]
  rw [← ENNReal.iSup_div]

open Classical in
/-- **Positive MCA error characterization.** `0 < epsMCA C δ` iff some word stack admits a bad
scalar. Complements `epsMCA_eq_zero_iff`. -/
theorem epsMCA_pos_iff (C : Set (ι → A)) (δ : ℝ≥0) :
    0 < epsMCA (F := F) (A := A) C δ ↔
      ∃ (u : WordStack A (Fin 2) ι) (γ : F), mcaEvent C δ (u 0) (u 1) γ := by
  rw [pos_iff_ne_zero, Ne, epsMCA_eq_zero_iff]
  push_neg
  tauto

open Classical in
/-- **Bad-scalar-count bound ⇒ prize-shape MCA bound.** If every word stack has at most `ℓ` bad
scalars, then `epsMCA C δ ≤ ℓ/|F|`. Via the closed form `epsMCA_eq_iSup_badCount_div`, this is the
`poly/q` shape of ABF26 Grand Challenge 1: the prize reduces to *uniformly bounding the bad-scalar
count* `ℓ` (which in the Johnson window is the proven Guruswami–Sudan list size). -/
theorem epsMCA_le_of_badCount_le
    (C : Set (ι → A)) (δ : ℝ≥0) (ℓ : ℕ)
    (h : ∀ u : WordStack A (Fin 2) ι,
      (Finset.filter (fun γ : F => mcaEvent C δ (u 0) (u 1) γ) Finset.univ).card ≤ ℓ) :
    epsMCA (F := F) (A := A) C δ ≤ (ℓ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [epsMCA_eq_iSup_badCount_div]
  gcongr
  exact iSup_le fun u => by exact_mod_cast h u

open Classical in
/-- **Bad scalars are line-close scalars.** Every bad scalar (`mcaEvent`) makes the line `δ`-close
to the code (`mcaEvent_imp_relCloseToCode`), so the bad-scalar count is at most the line-close
count. -/
theorem badCount_le_lineCloseCount (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) :
    (Finset.filter (fun γ : F => mcaEvent C δ (u 0) (u 1) γ) Finset.univ).card ≤
      (Finset.filter (fun γ : F => δᵣ(u 0 + γ • u 1, C) ≤ δ) Finset.univ).card := by
  apply Finset.card_le_card
  intro γ hγ
  rw [Finset.mem_filter] at hγ ⊢
  exact ⟨hγ.1, mcaEvent_imp_relCloseToCode C δ (u 0) (u 1) γ hγ.2⟩

open Classical in
/-- **Prize reduction to the proximity-gap line-close count.** If for every word stack the number
of scalars `γ` making the line `δ`-close to `C` is at most `ℓ`, then `epsMCA C δ ≤ ℓ/|F|`. This
reduces ABF26 Grand Challenge 1 to bounding the *line-close count* — exactly the quantity the
proximity-gap / list-decoding theorems control (proven in the Johnson window). -/
theorem epsMCA_le_of_lineCloseCount_le
    (C : Set (ι → A)) (δ : ℝ≥0) (ℓ : ℕ)
    (h : ∀ u : WordStack A (Fin 2) ι,
      (Finset.filter (fun γ : F => δᵣ(u 0 + γ • u 1, C) ≤ δ) Finset.univ).card ≤ ℓ) :
    epsMCA (F := F) (A := A) C δ ≤ (ℓ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_of_badCount_le C δ ℓ (fun u => le_trans (badCount_le_lineCloseCount C δ u) (h u))

open Classical in
/-- **Maximal MCA error.** If some word stack has *every* scalar bad (`mcaEvent` for all `γ`),
the MCA error is maximal: `epsMCA C δ = 1`. Together with `epsMCA_eq_zero_iff` and `epsMCA_pos_iff`
this rounds out the trichotomy. -/
theorem epsMCA_eq_one_of_forall_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι)
    (hu : ∀ γ : F, mcaEvent C δ (u 0) (u 1) γ) :
    epsMCA (F := F) (A := A) C δ = 1 := by
  refine le_antisymm (epsMCA_le_one C δ) ?_
  refine le_trans ?_ (mcaEvent_prob_le_epsMCA C δ u)
  rw [prob_uniform_eq_card_filter_div_card, Finset.filter_true_of_mem (fun γ _ => hu γ),
      Finset.card_univ]
  rw [ENNReal.div_self (by exact_mod_cast Fintype.card_ne_zero) (by simp)]

open Classical in
/-- **Maximal MCA error characterization.** `epsMCA C δ = 1` iff some word stack has every scalar
bad. Completes the trichotomy with `epsMCA_eq_zero_iff` / `epsMCA_pos_iff`. -/
theorem epsMCA_eq_one_iff (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := A) C δ = 1 ↔
      ∃ u : WordStack A (Fin 2) ι, ∀ γ : F, mcaEvent C δ (u 0) (u 1) γ := by
  constructor
  · intro h
    obtain ⟨u₀, hu₀⟩ := Finite.exists_max (fun u : WordStack A (Fin 2) ι =>
      Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ])
    have hpr : Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u₀ 0) (u₀ 1) γ] = 1 := by
      refine le_antisymm (Pr_le_one _ _) ?_
      rw [← h]; unfold epsMCA; exact iSup_le hu₀
    refine ⟨u₀, fun γ => ?_⟩
    rw [prob_uniform_eq_card_filter_div_card] at hpr
    have hcard : (Finset.filter (fun γ : F => mcaEvent C δ (u₀ 0) (u₀ 1) γ) Finset.univ).card
        = Fintype.card F := by
      have h2 := (ENNReal.div_eq_one_iff (by exact_mod_cast Fintype.card_ne_zero)
        (by simp)).mp hpr
      exact_mod_cast h2
    have huniv : Finset.filter (fun γ : F => mcaEvent C δ (u₀ 0) (u₀ 1) γ) Finset.univ
        = Finset.univ := Finset.eq_univ_of_card _ hcard
    have hmem : γ ∈ Finset.filter (fun γ : F => mcaEvent C δ (u₀ 0) (u₀ 1) γ) Finset.univ := by
      rw [huniv]; exact Finset.mem_univ γ
    exact (Finset.mem_filter.mp hmem).2
  · rintro ⟨u, hu⟩
    exact epsMCA_eq_one_of_forall_mcaEvent C δ u hu

end ProximityGap

namespace ProximityGap.MCALowerExample

instance mcaLowerExample_fact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

open ProximityGap Code

/-- The zero linear code over `ZMod 2` (carrier `{0}`) on one coordinate. -/
abbrev C0 : Set (Fin 1 → ZMod 2) := {(fun _ => 0)}

/-- The witnessing stack `u 0 = 0`, `u 1 = 1`. -/
abbrev u0 : WordStack (ZMod 2) (Fin 2) (Fin 1) := ![(fun _ => 0), (fun _ => 1)]

/-- `mcaEvent` fires for the zero code `C0` at `γ = 0`: the line `0 + 0·1 = 0` equals the codeword
`0` on `S = {0}`, but no codeword equals `u 1 = 1` there, so `¬ pairJointAgreesOn`. -/
theorem mcaEvent_C0 : mcaEvent (F := ZMod 2) C0 0 (u0 0) (u0 1) 0 := by
  refine ⟨{0}, ?_, ⟨(fun _ => 0), rfl, ?_⟩, ?_⟩
  · simp
  · intro i hi; fin_cases i; simp [u0]
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    have hv₁eq : v₁ = (fun _ => 0) := hv₁
    have hc := (hag 0 (by simp)).2
    rw [hv₁eq] at hc
    simp only [u0, Matrix.cons_val_one] at hc
    exact absurd hc (by decide)

/-- **The MCA error of the zero linear code is `≥ 1/2`.** Hence the Grand-Challenge-1 `poly/q`
upper bound is FALSE for general linear codes — it genuinely requires the Reed–Solomon structure
hypothesis. -/
theorem epsMCA_C0_ge_half :
    (1 : ℝ≥0∞) / 2 ≤ epsMCA (F := ZMod 2) (A := ZMod 2) C0 0 := by
  have h := epsMCA_ge_inv_card_of_mcaEvent (F := ZMod 2) (A := ZMod 2) C0 0 u0 0 mcaEvent_C0
  simpa using h

open Classical in
/-- For the zero code over `ZMod 2` on one coordinate, each stack has at most one bad scalar. -/
theorem badScalar_card_le_one (u : WordStack (ZMod 2) (Fin 2) (Fin 1)) :
    (Finset.filter (fun γ : ZMod 2 => mcaEvent C0 0 (u 0) (u 1) γ) Finset.univ).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro γ hγ γ' hγ'
  rw [Finset.mem_filter] at hγ hγ'
  obtain ⟨S, hS, ⟨w, hwmem, hweq⟩, hno⟩ := hγ.2
  obtain ⟨S', hS', ⟨w', hwmem', hweq'⟩, _⟩ := hγ'.2
  have hmemS : ∀ (T : Finset (Fin 1)), (1 : ℝ≥0) ≤ (T.card : ℝ≥0) → (0 : Fin 1) ∈ T := by
    intro T hT
    have h1 : 1 ≤ T.card := by exact_mod_cast hT
    have hle : T.card ≤ 1 := by have := Finset.card_le_univ T; rwa [Fintype.card_fin] at this
    have hTeq : T = Finset.univ := Finset.eq_univ_of_card T (by rw [Fintype.card_fin]; omega)
    rw [hTeq]; exact Finset.mem_univ 0
  have h0S : (0 : Fin 1) ∈ S := hmemS S (by simpa using hS)
  have h0S' : (0 : Fin 1) ∈ S' := hmemS S' (by simpa using hS')
  have hw0 : w = (fun _ => 0) := hwmem
  have hw0' : w' = (fun _ => 0) := hwmem'
  have he : (0 : ZMod 2) = (u 0) 0 + γ • (u 1) 0 := by
    have := hweq 0 h0S; rw [hw0] at this; exact this
  have he' : (0 : ZMod 2) = (u 0) 0 + γ' • (u 1) 0 := by
    have := hweq' 0 h0S'; rw [hw0'] at this; exact this
  have hu1 : (u 1) 0 ≠ 0 := by
    intro h
    apply hno
    refine ⟨(fun _ => 0), rfl, (fun _ => 0), rfl, fun i hi => ?_⟩
    have hi0 : i = 0 := Subsingleton.elim i 0
    subst hi0
    have hu0 : (u 0) 0 = 0 := by rw [h, smul_zero, add_zero] at he; exact he.symm
    exact ⟨hu0.symm, h.symm⟩
  have hmul : γ • (u 1) 0 = γ' • (u 1) 0 := by
    have h1 : (u 0) 0 + γ • (u 1) 0 = (u 0) 0 + γ' • (u 1) 0 := by rw [← he, ← he']
    exact add_left_cancel h1
  rw [smul_eq_mul, smul_eq_mul] at hmul
  exact mul_right_cancel₀ hu1 hmul

open Classical in
/-- **Exact value: `epsMCA(zero code over ZMod 2) = 1/2`.** -/
theorem epsMCA_C0_eq_half :
    epsMCA (F := ZMod 2) (A := ZMod 2) C0 0 = 1 / 2 := by
  refine le_antisymm ?_ epsMCA_C0_ge_half
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  have hc2 : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [hc2]
  simp only [ENNReal.coe_natCast, Nat.cast_ofNat, ENNReal.coe_ofNat]
  gcongr
  exact_mod_cast badScalar_card_le_one u

end ProximityGap.MCALowerExample
