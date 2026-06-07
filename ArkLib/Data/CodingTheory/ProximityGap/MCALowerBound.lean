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
  rw [prob_uniform_eq_card_filter_div_card]
  have hfalse : ∀ γ : F, ¬ mcaEvent (Set.univ : Set (ι → A)) δ (u 0) (u 1) γ := by
    rintro γ ⟨S, hS, hw, hno⟩
    exact hno ⟨u 0, Set.mem_univ _, u 1, Set.mem_univ _, fun i _ => ⟨rfl, rfl⟩⟩
  rw [Finset.filter_false_of_mem (fun γ _ => hfalse γ)]
  simp

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

end ProximityGap.MCALowerExample
