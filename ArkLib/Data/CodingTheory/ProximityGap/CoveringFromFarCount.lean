/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-! # Covering existence from a far-count bound (averaging double-count for CS25 #82)

Completes `exists_line_covered_stack_of_sum_far_lt`: over all stacks,
`∑_u #{γ : Δᵣ(u 0 + γ • u 1, C) > δ} = |F| · |ι → F| · |far|`, via the per-`γ` shift bijection
`u ↦ (u 0 + γ • u 1, u 1)`.  Hence a fully line-covered stack exists once
`|F| · |ι → F| · |far| < #stacks`, reducing #82's covering to the δ-neighbourhood bound. -/

open scoped NNReal BigOperators

namespace ProximityGap

open Code Finset

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- For fixed `γ`, stacks with a far line point biject with `far × (ι → F)` via the shift. -/
theorem card_far_stacks_fixed_gamma (C : Set (ι → F)) (δ : ℝ≥0) (γ : F) :
    (univ.filter (fun u : WordStack F (Fin 2) ι => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ)).card
      = (univ.filter (fun w : ι → F => ¬ δᵣ(w, C) ≤ δ)).card * Fintype.card (ι → F) := by
  classical
  rw [← Finset.card_univ (α := ι → F), ← Finset.card_product]
  refine Finset.card_equiv
    { toFun := fun u => (u 0 + γ • u 1, u 1)
      invFun := fun p => ![p.1 - γ • p.2, p.2]
      left_inv := fun u => by
        funext i; fin_cases i <;>
          simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, add_sub_cancel_right]
      right_inv := fun p => by
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, sub_add_cancel] }
    (fun u => by simp [mem_filter, mem_univ, mem_product, Equiv.coe_fn_mk])

/-- Double-count: `∑_u #{far γ} = |F| · |ι → F| · |far|`. -/
theorem sum_card_far_eq (C : Set (ι → F)) (δ : ℝ≥0) :
    (∑ u : WordStack F (Fin 2) ι,
        (univ.filter (fun γ : F => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ)).card)
      = Fintype.card F *
          (Fintype.card (ι → F) * (univ.filter (fun w : ι → F => ¬ δᵣ(w, C) ≤ δ)).card) := by
  classical
  simp only [card_filter]
  rw [Finset.sum_comm]
  have h : ∀ γ : F,
      (∑ u : WordStack F (Fin 2) ι, if ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ then 1 else 0)
        = (univ.filter (fun w : ι → F => ¬ δᵣ(w, C) ≤ δ)).card * Fintype.card (ι → F) := by
    intro γ
    rw [← card_far_stacks_fixed_gamma C δ γ, card_filter]
  simp_rw [h]
  rw [Finset.sum_const, card_univ, smul_eq_mul]
  ring

/-- **Covering existence from the far-count bound** (combine with the δ-neighbourhood bound). -/
set_option maxHeartbeats 400000 in
theorem exists_line_covered_stack_of_far_count_lt (C : Set (ι → F)) (δ : ℝ≥0)
    (hfew : Fintype.card F *
              (Fintype.card (ι → F) * (univ.filter (fun w : ι → F => ¬ δᵣ(w, C) ≤ δ)).card)
            < Fintype.card (WordStack F (Fin 2) ι)) :
    ∃ u : WordStack F (Fin 2) ι, ∀ γ : F, δᵣ(u 0 + γ • u 1, C) ≤ δ := by
  refine exists_line_covered_stack_of_sum_far_lt C δ ?_
  rw [sum_card_far_eq]
  exact hfew

end ProximityGap
