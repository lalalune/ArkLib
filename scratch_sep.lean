import Mathlib
open Finset

-- arithmetic: with 0 < b, b < a, a ≤ k ⇒ a - b < k
example (a b k : ℕ) (hb : 0 < b) (hba : b < a) (hak : a ≤ k) : a - b < k := by
  omega
