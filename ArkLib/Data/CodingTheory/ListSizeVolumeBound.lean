/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Elias list-size ≤ ball-volume bound

The number of `δ`-close codewords to a word is at most the q-ary Hamming-ball volume `Vol_q(δ,n)`,
in three forms: per-word (`closeCodewordsRel_ncard_le_hammingBallVolume`), maximised
`|Λ(C,δ)| ≤ Vol_q(δ,n)` (`Lambda_le_hammingBallVolume`), and as a `listDecodable` statement
(`listDecodable_hammingBallVolume`).  This is the elementary Elias upper bound: the close-codeword
set sits inside the radius-`⌊δn⌋` Hamming ball, whose cardinality is exactly the volume
(`hammingBallVolume_eq_ncard_hammingBall`).
-/

open ListDecodable

namespace CodingTheory

/-- **Elias upper bound (per-word).** The number of `δ`-close codewords of any code `C` to a word
`f` is at most the q-ary Hamming-ball volume `Vol_q(δ, n)`. -/
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

/-- **Maximised Elias bound `|Λ(C,δ)| ≤ Vol_q(δ,n)`.** -/
theorem Lambda_le_hammingBallVolume
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] {F : Type} [Fintype F] [DecidableEq F]
    (C : Code ι F) (δ : ℝ) :
    Lambda C δ ≤ (hammingBallVolume (Fintype.card F) δ (Fintype.card ι) : ℕ∞) := by
  apply Lambda_le_natCast_of_forall_ncard_le
  intro f
  exact closeCodewordsRel_ncard_le_hammingBallVolume C f δ

/-- **Every code is `(δ, Vol_q(δ,n))`-list-decodable** — the `listDecodable`-predicate form. -/
theorem listDecodable_hammingBallVolume
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] {F : Type} [Fintype F] [DecidableEq F]
    (C : Code ι F) (δ : ℝ) :
    listDecodable C δ ((hammingBallVolume (Fintype.card F) δ (Fintype.card ι) : ℕ) : ℝ) := by
  intro y
  exact_mod_cast closeCodewordsRel_ncard_le_hammingBallVolume C y δ

end CodingTheory

#print axioms CodingTheory.closeCodewordsRel_ncard_le_hammingBallVolume
#print axioms CodingTheory.Lambda_le_hammingBallVolume
#print axioms CodingTheory.listDecodable_hammingBallVolume
