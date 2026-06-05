import Mathlib.Tactic
import Mathlib.Algebra.IsPrimePow

-- Test the prime-power sequence: qs i = 2 ^ (i + n) is strictly mono, all prime powers, all ≥ 2^n.

example (n : ℕ) (hn : 1 ≤ n) :
    StrictMono (fun i => 2 ^ (i + n)) ∧
    (∀ i, IsPrimePow (2 ^ (i + n))) ∧
    (∀ i, 2 ^ n ≤ 2 ^ (i + n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    simp only
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · intro i
    have hp : IsPrimePow (2 : ℕ) := Nat.prime_two.isPrimePow
    exact hp.pow (by omega)
  · intro i
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
