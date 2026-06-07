/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-! # Covering existence — the averaging step toward a CS25 complete breakdown

This file isolates a single, fully general combinatorial brick used by the CS25 / ABF26 T4.17
complete correlated-agreement breakdown argument: if **few** words are far from a code `C`, then
some affine line `{u 0 + γ • u 1 : γ}` lies **entirely** within the `δ`-neighbourhood of `C`.

Combined with `ProximityGap.one_le_epsCA_of_line_covered` (given a non-jointly-close such stack)
this reduces the breakdown lower bound `1 ≤ ε_ca(C, δ, δ)` to the δ-neighbourhood-complement
bound `|F| · |{w : Δᵣ(w,C) > δ}| < |F|^{|ι|}` (the CS25 second-moment core).

The proof is a double-count / averaging argument:
`∑_{u} #{γ : u 0 + γ • u 1 far}  =  ∑_{γ} #{u : u 0 + γ • u 1 far}  =  |F| · |F|^{|ι|} · |far|`,
using for each fixed `γ` the shift bijection `u ↦ (u 0 + γ • u 1, u 1)` on stacks; when this is
`< |F|^{2|ι|} = #stacks`, some stack has zero far `γ`. -/

open scoped NNReal BigOperators

namespace CodingTheory.ProximityGap

open Code Finset

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- For a fixed `γ`, the stacks whose line point `u 0 + γ • u 1` is "far" (in `M`) are in
bijection with `M × (ι → F)` (choose the far value and the second row freely; the first row is
then forced).  Hence their count is `|M| · |ι → F|`. -/
theorem card_far_stacks_fixed_gamma (M : Finset (ι → F)) (γ : F) :
    (univ.filter (fun u : WordStack F (Fin 2) ι => u 0 + γ • u 1 ∈ M)).card
      = M.card * Fintype.card (ι → F) := by
  classical
  rw [← card_product]
  refine card_nbij' (fun u => (u 0 + γ • u 1, u 1))
    (fun p => ![p.1 - γ • p.2, p.2]) ?_ ?_ ?_ ?_
  · -- maps into `M ×ˢ univ`
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    simp only [mem_product, mem_filter, mem_univ, and_true]
    exact ⟨hu, mem_univ _⟩
  · -- inverse maps back into the filtered set
    intro p hp
    simp only [mem_product, mem_filter, mem_univ, true_and, and_true] at hp
    simp only [mem_filter, mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    have : p.1 - γ • p.2 + γ • p.2 = p.1 := by ring
    rw [this]; exact hp
  · -- left inverse
    intro u _
    funext i
    fin_cases i <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, add_sub_cancel_right]
  · -- right inverse
    intro p _
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, sub_add_cancel]

/-- **Double-count of far line points across all stacks.**
`∑_{u} #{γ : u 0 + γ • u 1 far}  =  |F| · |ι → F| · |M|`. -/
theorem sum_card_far_eq (M : Finset (ι → F)) :
    (∑ u : WordStack F (Fin 2) ι,
        (univ.filter (fun γ : F => u 0 + γ • u 1 ∈ M)).card)
      = Fintype.card F * (Fintype.card (ι → F) * M.card) := by
  classical
  simp only [card_filter]
  rw [Finset.sum_comm]
  have : ∀ γ : F,
      (∑ u : WordStack F (Fin 2) ι, if u 0 + γ • u 1 ∈ M then 1 else 0)
        = M.card * Fintype.card (ι → F) := by
    intro γ
    rw [← card_far_stacks_fixed_gamma M γ, card_filter]
  simp_rw [this]
  rw [Finset.sum_const, card_univ]
  ring

/-- **Averaging: a fully line-covered stack exists when few words are far from `C`.**

If `|F| · |{w : Δᵣ(w, C) > δ}| < |F|^{|ι|}` then some stack `u` has its entire affine line
`u 0 + γ • u 1` within relative distance `δ` of `C`.  This is the averaging half of the CS25
complete-breakdown construction; the remaining content is the δ-neighbourhood-complement bound
on `|{w : Δᵣ(w, C) > δ}|` (plus a non-jointness check), after which
`one_le_epsCA_of_line_covered` gives `ε_ca = 1`. -/
theorem exists_line_covered_stack_of_few_far (C : Set (ι → F)) (δ : ℝ≥0)
    (hfew : Fintype.card F *
              (univ.filter (fun w : ι → F => ¬ δᵣ(w, C) ≤ δ)).card
            < Fintype.card F ^ Fintype.card ι) :
    ∃ u : WordStack F (Fin 2) ι, ∀ γ : F, δᵣ(u 0 + γ • u 1, C) ≤ δ := by
  classical
  set M : Finset (ι → F) := univ.filter (fun w => ¬ δᵣ(w, C) ≤ δ) with hMdef
  by_contra hcon
  push_neg at hcon
  -- every stack has at least one far γ
  have h1 : ∀ u : WordStack F (Fin 2) ι,
      1 ≤ (univ.filter (fun γ : F => u 0 + γ • u 1 ∈ M)).card := by
    intro u
    obtain ⟨γ, hγ⟩ := hcon u
    refine card_pos.mpr ⟨γ, ?_⟩
    simp only [hMdef, mem_filter, mem_univ, true_and]
    exact hγ
  -- so #stacks ≤ ∑_u (far γ count) = |F| · |ι→F| · |M|
  have hcard : Fintype.card (WordStack F (Fin 2) ι)
      ≤ Fintype.card F * (Fintype.card (ι → F) * M.card) := by
    rw [← sum_card_far_eq M]
    calc Fintype.card (WordStack F (Fin 2) ι)
        = ∑ _u : WordStack F (Fin 2) ι, 1 := by rw [Finset.sum_const, card_univ, smul_eq_mul, mul_one]
      _ ≤ _ := Finset.sum_le_sum (fun u _ => h1 u)
  -- but #stacks = |F|^{2|ι|} and the count is |F| · |F|^{|ι|} · |M| = |F|·|M| · |F|^{|ι|} < |F|^{|ι|}·|F|^{|ι|}
  have hws : Fintype.card (WordStack F (Fin 2) ι) = Fintype.card F ^ Fintype.card ι * Fintype.card F ^ Fintype.card ι := by
    simp only [WordStack, Matrix, Fintype.card_pi, Fintype.card_fun, Finset.prod_const,
      Fintype.card_fin]
    ring
  have hiF : Fintype.card (ι → F) = Fintype.card F ^ Fintype.card ι := by
    rw [Fintype.card_fun]
  rw [hws, hiF] at hcard
  -- hcard : |F|^|ι| * |F|^|ι| ≤ |F| * (|F|^|ι| * |M|)
  -- hfew  : |F| * |M| < |F|^|ι|
  have hMcard : M.card = (univ.filter (fun w : ι → F => ¬ δᵣ(w, C) ≤ δ)).card := by rw [hMdef]
  rw [hMcard] at hcard
  nlinarith [hcard, hfew, Nat.zero_le (Fintype.card F ^ Fintype.card ι),
    Nat.zero_le (univ.filter (fun w : ι → F => ¬ δᵣ(w, C) ≤ δ)).card]

end CodingTheory.ProximityGap
