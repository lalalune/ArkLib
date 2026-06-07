/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Basic facts about Hamming balls (`ListDecodable.hammingBall` / `relHammingBall`)

Centre membership and radius monotonicity for the Hamming-ball *sets* defined in
`ListDecodability.lean` — foundational facts for covering / list-decoding arguments.
-/

namespace ListDecodable

variable {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]

/-- The centre of a Hamming ball lies in the ball (`hammingDist y y = 0 ≤ r`). -/
lemma self_mem_hammingBall (y : ι → F) (r : ℕ) : y ∈ hammingBall y r := by
  simp [hammingBall, hammingDist_self]

/-- The Hamming ball is monotone in its (absolute) radius. -/
lemma hammingBall_mono {y : ι → F} {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    hammingBall y r₁ ⊆ hammingBall y r₂ := by
  intro x hx
  simp only [hammingBall, Set.mem_setOf_eq] at hx ⊢
  exact le_trans hx h

/-- The relative Hamming ball is monotone in its (relative) radius. -/
lemma relHammingBall_mono {y : ι → F} {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    relHammingBall y r₁ ⊆ relHammingBall y r₂ := by
  intro x hx
  simp only [relHammingBall, Set.mem_setOf_eq] at hx ⊢
  exact le_trans hx h

end ListDecodable

#print axioms ListDecodable.self_mem_hammingBall
#print axioms ListDecodable.hammingBall_mono
#print axioms ListDecodable.relHammingBall_mono
