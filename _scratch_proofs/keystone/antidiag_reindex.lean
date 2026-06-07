theorem antidiag_reindex {M : Type*} [AddCommMonoid M] (t : ℕ) (f : ℕ × ℕ → M) :
  ∑ ab ∈ Finset.antidiagonal (t + 1), f ab
  = ∑ i1 ∈ Finset.range (t + 2), f (i1, t + 1 - i1) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]