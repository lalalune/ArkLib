import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityPrizeLeaves2
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

/-- For any target word on `j + 1` evaluation points and any excluded point
`x`, there is a degree-`< j` Reed-Solomon codeword agreeing with the target off
`x`. This is the interpolation step used in the JH01 list-size separation. -/
theorem exists_codeword_agree_off_point (j : ℕ) (domain : Fin (j + 1) ↪ F)
    (w : Fin (j + 1) → F) (x : Fin (j + 1)) :
    ∃ c ∈ ReedSolomon.code domain j, ∀ i, i ≠ x → c i = w i := by
  classical
  set S : Finset (Fin (j + 1)) := Finset.univ.filter (fun i => i ≠ x) with hS
  have hScard : S.card ≤ j := by
    have : S.card = j := by
      rw [hS, Finset.filter_ne']
      simp
    omega
  obtain ⟨c, hc_mem, hc_agree⟩ :=
    ReedSolomon.ReedSolomon_interpolate_through_subset (k := j) domain S hScard w
  refine ⟨c, hc_mem, ?_⟩
  intro i hi
  apply hc_agree
  rw [hS]
  simp [hi]

/-- If two words on `j + 1` positions agree away from one point, then they are
within relative Hamming radius `1 / (j + 1)`. -/
theorem mem_relHammingBall_of_agree_off_point (j : ℕ) (w c : Fin (j + 1) → F)
    (x : Fin (j + 1)) (hagree : ∀ i, i ≠ x → c i = w i) :
    c ∈ ListDecodable.relHammingBall w (1 / (j + 1 : ℝ)) := by
  classical
  have hn_pos : 0 < Fintype.card (Fin (j + 1)) := Fintype.card_pos
  have hdist : hammingDist w c ≤ 1 := by
    have hfsub : Finset.univ.filter (fun i => w i ≠ c i) ⊆ {x} := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_contra hix
      simp only [Finset.mem_singleton] at hix
      exact hi ((hagree i hix).symm)
    have heq : hammingDist w c = (Finset.univ.filter (fun i => w i ≠ c i)).card := by
      rw [hammingDist]
      rfl
    rw [heq]
    calc (Finset.univ.filter (fun i => w i ≠ c i)).card
        ≤ ({x} : Finset (Fin (j + 1))).card := Finset.card_le_card hfsub
      _ = 1 := Finset.card_singleton x
  simp only [ListDecodable.relHammingBall, Set.mem_setOf_eq, Code.relHammingDist, NNRat.cast_div,
    NNRat.cast_natCast]
  rw [div_le_iff₀ (by exact_mod_cast hn_pos :
    (0 : ℝ) < (Fintype.card (Fin (j + 1)) : ℝ))]
  have hn : (Fintype.card (Fin (j + 1)) : ℝ) = (j : ℝ) + 1 := by simp
  rw [hn]
  have hd : (hammingDist w c : ℝ) ≤ 1 := by exact_mod_cast hdist
  have hcancel : (1 / (j + 1 : ℝ)) * ((j : ℝ) + 1) = 1 := by
    field_simp
  rw [hcancel]
  convert hd using 2
  congr!

end ReedSolomon
end CodingTheory
