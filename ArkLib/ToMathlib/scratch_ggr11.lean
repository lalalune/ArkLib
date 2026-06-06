import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace ScratchGGR11

/-- The GGR11 leaf-counting recursion (Theorem 3.6 of GGR11). -/
theorem tree_count_le
    (L : ℕ∞) (t : ℕ → ℕ → ℕ∞)
    (hbase : ∀ b, t b 0 ≤ 1)
    (hrec0 : ∀ r, t 0 (r + 1) ≤ L * t 0 r)
    (hrec : ∀ b r, t (b + 1) (r + 1) ≤ t b (r + 1) + L * t (b + 1) r) :
    ∀ b r, t b r ≤ ((b + r).choose r : ℕ∞) * L ^ r := by
  intro b r
  induction r generalizing b with
  | zero => simpa using hbase b
  | succ r ih =>
    induction b with
    | zero =>
      calc t 0 (r + 1)
          ≤ L * t 0 r := hrec0 r
        _ ≤ L * (((0 + r).choose r : ℕ∞) * L ^ r) := by gcongr; exact ih 0
        _ = ((0 + r).choose r : ℕ∞) * L ^ (r + 1) := by ring
        _ = ((0 + (r + 1)).choose (r + 1) : ℕ∞) * L ^ (r + 1) := by
              simp [Nat.choose_self]
    | succ b ihb =>
      calc t (b + 1) (r + 1)
          ≤ t b (r + 1) + L * t (b + 1) r := hrec b r
        _ ≤ ((b + (r + 1)).choose (r + 1) : ℕ∞) * L ^ (r + 1)
              + L * (((b + 1) + r).choose r * L ^ r) := by
              refine add_le_add ihb ?_
              exact mul_le_mul' (le_refl L) (ih (b + 1))
        _ = (((b + (r + 1)).choose (r + 1) : ℕ∞) + ((b + 1 + r).choose r : ℕ∞)) * L ^ (r + 1) := by
              ring
        _ = (((b + 1) + (r + 1)).choose (r + 1) : ℕ∞) * L ^ (r + 1) := by
              congr 1
              have : (b + 1) + (r + 1) = (b + (r + 1)) + 1 := by ring
              rw [this, Nat.choose_succ_succ (b + (r + 1)) r]
              push_cast
              have e1 : b + (r + 1) = b + r + 1 := by ring
              have e2 : b + 1 + r = b + r + 1 := by ring
              rw [e1, e2]
              ring

end ScratchGGR11
