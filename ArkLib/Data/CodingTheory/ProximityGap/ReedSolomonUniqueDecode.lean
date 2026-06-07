/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.TwoLineExtraction
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Reed–Solomon unique decoding (concrete instantiation)

Instantiating the abstract linear-code unique-decoding theorems
(`ProximityGap.codeword_eq_of_agree_minDist`, `ProximityGap.eq_of_close_to_common`,
`ProximityGap.closeCodewords_subsingleton`) at the concrete Reed–Solomon minimum distance
`minDist(RS[n,k]) = |ι| − k + 1` (`ReedSolomon.minDist_eq'`):

* `ReedSolomon.code_eq_of_agree` — two degree-`< k` RS codewords agreeing on `≥ k` evaluation points
  are equal (a degree-`< k` polynomial is pinned by `k` evaluations);
* `ReedSolomon.unique_decode` — the RS ball of radius `< (|ι|−k+1)/2` contains at most one codeword.

These are fully self-contained named Reed–Solomon results with no abstract hypotheses.
-/

namespace ReedSolomon

open ProximityGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F] [DecidableEq F]

/-- **Reed–Solomon unique decoding (agreement form).**  Two RS codewords of degree `< k` that agree
on more than `k − 1` evaluation points are equal.  (Instantiates the abstract unique-decoding
theorem with `minDist(RS) = |ι| − k + 1`.) -/
theorem code_eq_of_agree {α : ι ↪ F} {k : ℕ} [NeZero k] (hk : k ≤ Fintype.card ι)
    {c c' : ι → F} (hc : c ∈ ReedSolomon.code α k) (hc' : c' ∈ ReedSolomon.code α k)
    {S : Finset ι} (hagree : ∀ i ∈ S, c i = c' i) (hS : k - 1 < S.card) :
    c = c' := by
  refine codeword_eq_of_agree_minDist (ReedSolomon.code α k) hc hc' hagree ?_
  rw [minDist_eq' hk]
  omega

/-- **Reed–Solomon unique decoding (ball form).**  The RS ball of radius `e` with `2e < |ι| − k + 1`
contains at most one codeword: two RS codewords within distance `e` of a common word coincide. -/
theorem unique_decode {α : ι ↪ F} {k : ℕ} [NeZero k] (hk : k ≤ Fintype.card ι)
    {f c c' : ι → F} {e : ℕ}
    (hc : c ∈ ReedSolomon.code α k) (hc' : c' ∈ ReedSolomon.code α k)
    (hd : hammingDist f c ≤ e) (hd' : hammingDist f c' ≤ e)
    (he : 2 * e < Fintype.card ι - k + 1) :
    c = c' := by
  refine eq_of_close_to_common (ReedSolomon.code α k) hc hc' hd hd' ?_
  rw [minDist_eq' hk]
  exact he

end ReedSolomon
