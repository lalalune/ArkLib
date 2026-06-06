import Mathlib
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon

open Polynomial BigOperators Finset

namespace BKR06ScratchTest

open ListDecodable

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

-- hammingDist via disagreement filter (the exact mathlib unfolding)
example (w c : ι → F) : hammingDist w c = (Finset.univ.filter (fun i => w i ≠ c i)).card := rfl

-- agreement set ≥ a  ⟹  hammingDist ≤ N - a
example (w c : ι → F) (a : ℕ)
    (hagree : a ≤ (Finset.univ.filter (fun i => w i = c i)).card) :
    hammingDist w c ≤ Fintype.card ι - a := by
  classical
  have hsplit :
      (Finset.univ.filter (fun i => w i = c i)).card
        + (Finset.univ.filter (fun i => ¬ (w i = c i))).card
        = Fintype.card ι := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hham : hammingDist w c = (Finset.univ.filter (fun i => ¬ (w i = c i))).card := rfl
  omega

-- closeness from hammingDist ≤ floor bound (handle the Decidable diamond)
example (w c : ι → F) (δ : ℝ)
    (hδ : (hammingDist w c : ℝ) / Fintype.card ι ≤ δ) :
    c ∈ relHammingBall w δ := by
  classical
  simp only [relHammingBall, Set.mem_setOf_eq, Code.relHammingDist]
  rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
  exact hδ

end BKR06ScratchTest
