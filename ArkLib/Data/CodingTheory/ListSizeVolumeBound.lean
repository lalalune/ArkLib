import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.ListDecodability
open ListDecodable
namespace CodingTheory

/-- **Elias upper bound (list size ≤ ball volume).** The number of `δ`-close codewords of any
code `C` to a word `f` is at most the q-ary Hamming-ball volume `Vol_q(δ, n)`: the close-codeword
set sits inside the radius-`⌊δn⌋` Hamming ball, whose cardinality is exactly the volume. -/
theorem closeCodewordsRel_ncard_le_hammingBallVolume
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] {F : Type} [Fintype F] [DecidableEq F]
    (C : Code ι F) (f : ι → F) (δ : ℝ) :
    (closeCodewordsRel C f δ).ncard ≤ hammingBallVolume (Fintype.card F) δ (Fintype.card ι) := by
  rw [hammingBallVolume_eq_ncard_hammingBall δ f]
  refine Set.ncard_le_ncard (fun c hc => ?_) (Set.toFinite _)
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hball := hc.2
  simp only [relHammingBall, Set.mem_setOf_eq, Code.relHammingDist] at hball
  push_cast at hball
  rw [div_le_iff₀ hn] at hball
  simp only [hammingBall, Set.mem_setOf_eq]
  exact Nat.le_floor hball

end CodingTheory
#print axioms CodingTheory.closeCodewordsRel_ncard_le_hammingBallVolume
