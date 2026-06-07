/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAZeroCodeExact
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# Grand Challenge guardrails from the exact zero-code MCA value

`MCAZeroCodeExact.lean` proves that the zero code over a finite field has
`ε_mca(⊥, 0) = 1 / |F|`.  This file exposes the consumer-facing consequence for the Grand
Challenge witness API: whenever the target threshold is below `1 / |F|`, the zero code gives an
upper witness at radius `0`.

This is a guardrail for the refuted black-box line-decoding statement: it packages the exact
zero-code value as a one-sided obstruction, without asserting any Guruswami--Sudan extraction or
repairing ABF26 Theorem 4.21.
-/

namespace ProximityGap.MCAZeroCode

open scoped NNReal ENNReal

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

section General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Zero-code upper witness from the exact value.** If the target `ε_star` is below `1 / |F|`,
then the zero code has already exceeded the target at radius `0`. -/
def MCAUpperWitness_bot_of_lt_inv_card (ε_star : ℝ≥0)
    (hε : (ε_star : ENNReal) < (1 : ENNReal) / (Fintype.card F : ENNReal)) :
    GrandChallenges.MCAUpperWitness (F := F)
      (Cbot (ι := ι) (F := F) : Set (ι → F)) ε_star :=
  GrandChallenges.MCAUpperWitness.ofGt
    (C := (Cbot (ι := ι) (F := F) : Set (ι → F))) (δ := (0 : ℝ≥0)) <| by
      rw [epsMCA_bot_eq_inv_card]
      exact hε

/-- Existential form of `MCAUpperWitness_bot_of_lt_inv_card`, preserving the certified radius. -/
theorem exists_MCAUpperWitness_bot_of_lt_inv_card (ε_star : ℝ≥0)
    (hε : (ε_star : ENNReal) < (1 : ENNReal) / (Fintype.card F : ENNReal)) :
    ∃ w : GrandChallenges.MCAUpperWitness (F := F)
        (Cbot (ι := ι) (F := F) : Set (ι → F)) ε_star,
      w.δ = 0 :=
  ⟨MCAUpperWitness_bot_of_lt_inv_card (ι := ι) (F := F) ε_star hε, rfl⟩

/-- `epsStar` specialization of the zero-code upper witness. -/
noncomputable def MCAUpperWitness_bot_epsStar_of_lt_inv_card
    (hε : (epsStar : ENNReal) < (1 : ENNReal) / (Fintype.card F : ENNReal)) :
    GrandChallenges.MCAUpperWitness (F := F)
      (Cbot (ι := ι) (F := F) : Set (ι → F)) epsStar :=
  MCAUpperWitness_bot_of_lt_inv_card (ι := ι) (F := F) epsStar hε

/-- Existential `epsStar` specialization, preserving the certified radius `0`. -/
theorem exists_MCAUpperWitness_bot_epsStar_of_lt_inv_card
    (hε : (epsStar : ENNReal) < (1 : ENNReal) / (Fintype.card F : ENNReal)) :
    ∃ w : GrandChallenges.MCAUpperWitness (F := F)
        (Cbot (ι := ι) (F := F) : Set (ι → F)) epsStar,
      w.δ = 0 :=
  ⟨MCAUpperWitness_bot_epsStar_of_lt_inv_card (ι := ι) (F := F) hε, rfl⟩

end General

/-! ## Source audit -/

#print axioms MCAUpperWitness_bot_of_lt_inv_card
#print axioms exists_MCAUpperWitness_bot_of_lt_inv_card
#print axioms MCAUpperWitness_bot_epsStar_of_lt_inv_card
#print axioms exists_MCAUpperWitness_bot_epsStar_of_lt_inv_card

end ProximityGap.MCAZeroCode
