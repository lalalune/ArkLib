import Mathlib

open Finset

open scoped Classical in
example {G : Type*} [CommGroup G] [Fintype G] [IsCyclic G] (d : ℕ) (c : G) :
    (Finset.univ.filter fun x : G => x ^ d = c).card = 0 ∨
    (Finset.univ.filter fun x : G => x ^ d = c).card = Nat.gcd d (Fintype.card G) := by
  classical
  by_cases hc : c ∈ Set.range (powMonoidHom d : G →* G)
  · right
    -- nonempty fiber: equals fiber over 1, which is the kernel
    have h1 : (1 : G) ∈ Set.range (powMonoidHom d : G →* G) := ⟨1, by simp⟩
    have hfib : (Finset.univ.filter fun x : G => (powMonoidHom d : G →* G) x = c).card
        = (Finset.univ.filter fun x : G => (powMonoidHom d : G →* G) x = 1).card :=
      MonoidHom.card_fiber_eq_of_mem_range (powMonoidHom d : G →* G) hc h1
    have hker : Nat.card (powMonoidHom d : G →* G).ker = (Nat.card G).gcd d :=
      IsCyclic.card_powMonoidHom_ker G d
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype] at hker
    -- rewrite filter predicate
    have e1 : (Finset.univ.filter fun x : G => x ^ d = c)
        = (Finset.univ.filter fun x : G => (powMonoidHom d : G →* G) x = c) := by
      apply Finset.filter_congr; intro x _; simp [powMonoidHom_apply]
    have e2 : (Finset.univ.filter fun x : G => (powMonoidHom d : G →* G) x = 1)
        = (Finset.univ.filter fun x : G => x ∈ (powMonoidHom d : G →* G).ker) := by
      apply Finset.filter_congr; intro x _; simp [MonoidHom.mem_ker]
    rw [e1, hfib, e2, hker, Nat.gcd_comm]
  · left
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _
    intro hx
    exact hc ⟨x, by simpa [powMonoidHom_apply] using hx⟩
