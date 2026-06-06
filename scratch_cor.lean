import Mathlib

open Finset

open scoped Classical in
theorem L1 {G : Type*} [CommGroup G] [Fintype G] [IsCyclic G] (d : ℕ) (c : G) :
    (Finset.univ.filter fun x : G => x ^ d = c).card = 0 ∨
    (Finset.univ.filter fun x : G => x ^ d = c).card = Nat.gcd d (Fintype.card G) := by
  classical
  by_cases hc : c ∈ Set.range (powMonoidHom d : G →* G)
  · right
    have h1 : (1 : G) ∈ Set.range (powMonoidHom d : G →* G) := ⟨1, by simp⟩
    have hfib : (Finset.univ.filter fun x : G => (powMonoidHom d : G →* G) x = c).card
        = (Finset.univ.filter fun x : G => (powMonoidHom d : G →* G) x = 1).card :=
      MonoidHom.card_fiber_eq_of_mem_range (powMonoidHom d : G →* G) hc h1
    have hker : Nat.card (powMonoidHom d : G →* G).ker = (Nat.card G).gcd d :=
      IsCyclic.card_powMonoidHom_ker G d
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype] at hker
    have e1 : (Finset.univ.filter fun x : G => x ^ d = c)
        = (Finset.univ.filter fun x : G => (powMonoidHom d : G →* G) x = c) := by
      apply Finset.filter_congr; intro x _; simp [powMonoidHom_apply]
    have e2 : (Finset.univ.filter fun x : G => (powMonoidHom d : G →* G) x = 1)
        = (Finset.univ.filter fun x : G => x ∈ (powMonoidHom d : G →* G).ker) := by
      apply Finset.filter_congr; intro x _; simp [MonoidHom.mem_ker]
    rw [e1, hfib, e2, hker, Nat.gcd_comm]
  · left
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x _ hx
    exact hc ⟨x, by simpa [powMonoidHom_apply] using hx⟩

-- Corollary: binomial agreement c₁ x^a = c₂ x^b reduces to x^(a-b) = c₂ c₁⁻¹.
open scoped Classical in
theorem cor {G : Type*} [CommGroup G] [Fintype G] [IsCyclic G]
    (c₁ c₂ : G) (a b : ℕ) (hba : b < a) :
    (Finset.univ.filter fun x : G => c₁ * x ^ a = c₂ * x ^ b).card = 0 ∨
    (Finset.univ.filter fun x : G => c₁ * x ^ a = c₂ * x ^ b).card = Nat.gcd (a - b) (Fintype.card G) := by
  classical
  -- the predicate c₁ x^a = c₂ x^b ↔ x^(a-b) = c₂ c₁⁻¹
  have key : (Finset.univ.filter fun x : G => c₁ * x ^ a = c₂ * x ^ b)
      = (Finset.univ.filter fun x : G => x ^ (a - b) = c₂ * c₁⁻¹) := by
    apply Finset.filter_congr
    intro x _
    have hab : a = (a - b) + b := (Nat.sub_add_cancel hba.le).symm
    have hsplit : x ^ a = x ^ (a - b) * x ^ b := by rw [← pow_add, ← hab]
    rw [hsplit]
    constructor
    · intro h
      -- from c₁ * (x^(a-b) * x^b) = c₂ * x^b, cancel x^b and rearrange
      have hx : c₁ * x ^ (a - b) = c₂ := by
        have h' : (c₁ * x ^ (a - b)) * x ^ b = c₂ * x ^ b := by rw [mul_assoc]; exact h
        exact mul_right_cancel h'
      rw [eq_mul_inv_iff_mul_eq, mul_comm, hx]
    · intro h
      -- x^(a-b) = c₂ c₁⁻¹  →  c₁ * (x^(a-b) * x^b) = c₂ * x^b
      have hcoef : c₁ * (c₂ * c₁⁻¹) = c₂ := by
        rw [mul_comm c₂, ← mul_assoc, mul_inv_cancel, one_mul]
      rw [h, ← mul_assoc, hcoef]
  rw [key]
  exact L1 (a - b) (c₂ * c₁⁻¹)

-- The ≤ a-b leg.
open scoped Classical in
theorem cor_le {G : Type*} [CommGroup G] [Fintype G] [IsCyclic G]
    (c₁ c₂ : G) (a b : ℕ) (hba : b < a) :
    (Finset.univ.filter fun x : G => c₁ * x ^ a = c₂ * x ^ b).card ≤ a - b := by
  classical
  rcases cor c₁ c₂ a b hba with h | h
  · rw [h]; exact Nat.zero_le _
  · rw [h]
    exact Nat.le_of_dvd (Nat.sub_pos_of_lt hba) (Nat.gcd_dvd_left _ _)
