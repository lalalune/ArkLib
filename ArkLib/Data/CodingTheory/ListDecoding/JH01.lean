import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Tactic

/-!
# JH01 List-Decoding Separation Helpers

Small Reed-Solomon facts used by the JH01 list-size separation route.
-/

namespace CodingTheory
namespace ReedSolomon

variable {F : Type} [Field F]

/-- A Reed-Solomon code of degree bound `j` evaluated on `j + 1` points is a
proper submodule of the full word space, hence some word is not a codeword. -/
theorem exists_word_not_mem_code_of_length_succ (j : ℕ) (domain : Fin (j + 1) ↪ F) :
    ∃ w : Fin (j + 1) → F, w ∉ ReedSolomon.code domain j := by
  have hdim : Module.finrank F (ReedSolomon.code domain j) = j := by
    have h : j ≤ Fintype.card (Fin (j + 1)) := by simp
    simpa [LinearCode.dim] using ReedSolomon.dim_eq_deg_of_le' (α := domain) h
  have hne : ReedSolomon.code domain j ≠ ⊤ := by
    intro htop
    have : Module.finrank F (ReedSolomon.code domain j) = j + 1 := by
      rw [htop]
      simp
    omega
  by_contra hmiss
  push Not at hmiss
  apply hne
  refine le_antisymm le_top ?_
  intro w _
  exact hmiss w

end ReedSolomon
end CodingTheory
