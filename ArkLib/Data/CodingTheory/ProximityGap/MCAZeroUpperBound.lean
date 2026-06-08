/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# The `δ = 0` MCA upper bound, from scratch (Table-1 row 1, #232 positive side)

ABF26 Table 1, first row. We prove the from-scratch upper bound

  `ε_mca(C, 0) ≤ 1/|F|`     (`epsMCA_zero_le_inv`)

for **every** `F`-submodule code `C` — no admit, axiom-clean. At `δ = 0` the witness
set is forced to be all of `ι`, so a "bad" scalar `γ` is one with `u₀ + γ·u₁ ∈ C`
but not both `u₀, u₁ ∈ C`; at most one such `γ` exists (two would force `u₁ ∈ C`,
then `u₀ ∈ C`). Hence the bad-scalar count is `≤ 1` for every stack, and
`ε_mca ≤ 1/|F|`.

Combined with `rs_mcaUpperWitness` (near capacity), this gives an admit-free two-sided bracket on
the Grand MCA threshold: `0 ≤ δ* ≤ 1 − (k+1)/n`. The lower end is the matched
`MCALowerWitness` `rs_mcaLowerWitness_zero` (for `|F| ≥ 2^128`).

All results are hole-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. #232.
-/

namespace ProximityGap

open scoped NNReal ENNReal
open Code

-- The numeric `epsMCA` bridge uses the finite alphabet instance at proof time through the
-- probability API, matching the convention in `Errors.lean`.
set_option linter.unusedFintypeInType false

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F]
variable {A : Type} [Fintype A] [AddCommGroup A] [Module F A]

open Classical in
/-- **The `δ = 0` MCA upper bound (from scratch).** Every `F`-submodule code satisfies
`ε_mca(C, 0) ≤ 1/|F|`. -/
theorem epsMCA_zero_le_inv (C : Submodule F (ι → A)) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) 0 ≤ 1 / (Fintype.card F : ℝ≥0∞) := by
  have huniv : ∀ {S : Finset ι},
      ((1 - (0 : ℝ≥0)) * Fintype.card ι ≤ (S.card : ℝ≥0)) → S = Finset.univ := by
    intro S hS
    have hge : (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) := by simpa using hS
    have hgeN : Fintype.card ι ≤ S.card := by exact_mod_cast hge
    have hle : S.card ≤ Fintype.card ι := by simpa using Finset.card_le_univ S
    exact Finset.eq_univ_of_card S (le_antisymm hle hgeN)
  have key : ∀ u : WordStack A (Fin 2) ι,
      (Finset.filter (fun γ : F => mcaEvent (C : Set (ι → A)) 0 (u 0) (u 1) γ)
        Finset.univ).card ≤ 1 := by
    intro u
    rw [Finset.card_le_one]
    intro γ₁ hγ₁ γ₂ hγ₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ₁ hγ₂
    obtain ⟨S₁, hS₁card, ⟨w₁, hw₁C, hw₁⟩, hno₁⟩ := hγ₁
    obtain ⟨S₂, hS₂card, ⟨w₂, hw₂C, hw₂⟩, _⟩ := hγ₂
    have hS₁ := huniv hS₁card
    have hmem₁ : u 0 + γ₁ • u 1 ∈ C := by
      have he : w₁ = u 0 + γ₁ • u 1 := by
        funext i; have := hw₁ i (by rw [hS₁]; exact Finset.mem_univ i); simpa using this
      rw [he] at hw₁C; exact hw₁C
    have hmem₂ : u 0 + γ₂ • u 1 ∈ C := by
      have he : w₂ = u 0 + γ₂ • u 1 := by
        funext i
        have := hw₂ i (by rw [huniv hS₂card]; exact Finset.mem_univ i)
        simpa using this
      rw [he] at hw₂C; exact hw₂C
    by_contra hne
    have hd : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
    have hdiff : (γ₁ - γ₂) • u 1 ∈ C := by
      have he : (γ₁ - γ₂) • u 1 =
          (u 0 + γ₁ • u 1) - (u 0 + γ₂ • u 1) := by
        rw [sub_smul]
        abel
      rw [he]; exact C.sub_mem hmem₁ hmem₂
    have hu1 : u 1 ∈ C := by
      have := C.smul_mem (γ₁ - γ₂)⁻¹ hdiff
      rwa [inv_smul_smul₀ hd] at this
    have hu0 : u 0 ∈ C := by
      have he : u 0 = (u 0 + γ₁ • u 1) - γ₁ • u 1 := by abel
      rw [he]; exact C.sub_mem hmem₁ (C.smul_mem γ₁ hu1)
    exact hno₁ ⟨u 0, hu0, u 1, hu1, fun i _ => ⟨rfl, rfl⟩⟩
  have hmain := epsMCA_le_of_badCount_le (F := F) (A := A) (C : Set (ι → A)) 0 1 key
  simpa using hmain

/-- **Matched `MCALowerWitness` at `δ = 0`.** For a field with `|F| ≥ 2^128`,
radius `0` certifies `ε_mca(RS, 0) ≤ ε*` (`ε* = 2^{-128}`), so any resolution's
threshold satisfies `δ* ≥ 0`. -/
noncomputable def rs_mcaLowerWitness_zero {n : ℕ} [NeZero n] (domain : Fin n ↪ F) (k : ℕ)
    (hF : (2 : ℝ≥0∞) ^ 128 ≤ (Fintype.card F : ℝ≥0∞)) :
    GrandChallenges.MCALowerWitness
      (ReedSolomon.code (domain := domain) k : Set (Fin n → F)) epsStar where
  δ := 0
  le_one := zero_le_one
  bound := by
    refine le_trans (epsMCA_zero_le_inv (ReedSolomon.code (domain := domain) k)) ?_
    have hcoe : (epsStar : ENNReal) = 1 / 2 ^ 128 := by
      rw [epsStar, ENNReal.coe_div (by positivity), ENNReal.coe_one,
        ENNReal.coe_pow, ENNReal.coe_ofNat]
    rw [hcoe]
    exact ENNReal.div_le_div_left hF 1

#print axioms epsMCA_zero_le_inv
#print axioms rs_mcaLowerWitness_zero

end ProximityGap
