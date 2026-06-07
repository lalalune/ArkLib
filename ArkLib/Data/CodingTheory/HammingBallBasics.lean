/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Basic facts about Hamming balls (`ListDecodable.hammingBall` / `relHammingBall`)

Centre membership, radius monotonicity, and the zero-radius singleton for the Hamming-ball
*sets* from `ListDecodability.lean` — foundational facts for covering / list-decoding arguments.
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

/-- A zero-radius Hamming ball is the singleton of its centre. -/
lemma hammingBall_zero (y : ι → F) : hammingBall y 0 = {y} := by
  ext x
  simp only [hammingBall, Set.mem_setOf_eq, Nat.le_zero, hammingDist_eq_zero,
    Set.mem_singleton_iff]
  exact eq_comm

end ListDecodable

#print axioms ListDecodable.self_mem_hammingBall
#print axioms ListDecodable.hammingBall_mono
#print axioms ListDecodable.relHammingBall_mono
#print axioms ListDecodable.hammingBall_zero
