/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace CodeGeometry
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def emb (w : ι → α) : ι × α → ℝ :=
  fun p => (if w p.1 = p.2 then 1 else 0) - 1 / (Fintype.card α : ℝ)

noncomputable def codeInner (u v : ι → α) : ℝ := ∑ p : ι × α, emb u p * emb v p
def agree (u v : ι → α) : ℕ := (Finset.univ.filter (fun i => u i = v i)).card

/-- Per-coordinate inner-product identity. -/
private lemma row_identity (u v : ι → α) (i : ι) (hq : 0 < Fintype.card α) :
    (∑ a : α, ((if u i = a then (1:ℝ) else 0) - 1/(Fintype.card α:ℝ))
              * ((if v i = a then 1 else 0) - 1/(Fintype.card α:ℝ)))
      = (if u i = v i then (1:ℝ) else 0) - 1/(Fintype.card α:ℝ) := by
  classical
  set q : ℝ := (Fintype.card α : ℝ) with hqdef
  have hqne : q ≠ 0 := by positivity
  have hprod : ∀ a : α, ((if u i = a then (1:ℝ) else 0) - 1/q) * ((if v i = a then 1 else 0) - 1/q)
      = (if u i = a then (1:ℝ) else 0) * (if v i = a then 1 else 0)
        - (1/q) * (if u i = a then (1:ℝ) else 0)
        - (1/q) * (if v i = a then (1:ℝ) else 0)
        + (1/q)*(1/q) := by intro a; ring
  rw [Finset.sum_congr rfl (fun a _ => hprod a)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  -- ∑ indicator products = if u i = v i then 1 else 0
  have h1 : (∑ a : α, (if u i = a then (1:ℝ) else 0) * (if v i = a then 1 else 0))
      = if u i = v i then 1 else 0 := by
    rw [Finset.sum_eq_single (u i)]
    · by_cases h : u i = v i <;> simp [h, eq_comm]
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h2 : (∑ a : α, (1/q) * (if u i = a then (1:ℝ) else 0)) = 1/q := by
    rw [← Finset.mul_sum]; simp [Finset.sum_ite_eq']
  have h3 : (∑ a : α, (1/q) * (if v i = a then (1:ℝ) else 0)) = 1/q := by
    rw [← Finset.mul_sum]; simp [Finset.sum_ite_eq']
  have h4 : (∑ _a : α, (1/q)*(1/q)) = 1/q := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hqdef]
    field_simp
  rw [h1, h2, h3, h4]; ring

theorem codeInner_eq_agree_sub (u v : ι → α) (hq : 0 < Fintype.card α) :
    codeInner u v = (agree u v : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ) := by
  classical
  rw [codeInner, Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (fun i _ => by
    simpa [emb] using row_identity u v i hq)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [agree, Finset.card_filter, Nat.cast_sum, ← div_eq_mul_inv]
  congr 1
  apply Finset.sum_congr rfl; intro i _; by_cases h : u i = v i <;> simp [h]

/-- **Constant norm.** `⟨x_w, x_w⟩ = n(1 − 1/q)` (every coordinate agrees with
itself). -/
theorem codeInner_self (w : ι → α) (hq : 0 < Fintype.card α) :
    codeInner w w = (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) := by
  have hself : agree w w = Fintype.card ι := by
    rw [agree]
    simp [Finset.filter_true_of_mem, Finset.card_univ]
  rw [codeInner_eq_agree_sub w w hq, hself]
  have hqne : (Fintype.card α : ℝ) ≠ 0 := by positivity
  field_simp

/-- **The Plotkin / positive-semidefiniteness inequality.** For any finite
family of words, the Gram-sum of their simplex embeddings is nonnegative:
`∑ i ∑ j ⟨x_{c i}, x_{c j}⟩ = ‖∑ i x_{c i}‖² ≥ 0`. This is the engine of the
quadratic-in-`L` counting in Johnson-type list-size bounds. -/
theorem sum_sum_codeInner_nonneg {L : ℕ} (c : Fin L → ι → α) :
    0 ≤ ∑ i, ∑ j, codeInner (c i) (c j) := by
  classical
  have hswap : (∑ i, ∑ j, codeInner (c i) (c j))
      = ∑ p : ι × α, (∑ i, emb (c i) p) ^ 2 := by
    calc (∑ i, ∑ j, codeInner (c i) (c j))
        = ∑ i, ∑ j, ∑ p : ι × α, emb (c i) p * emb (c j) p := rfl
      _ = ∑ i, ∑ p : ι × α, ∑ j, emb (c i) p * emb (c j) p := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact Finset.sum_comm
      _ = ∑ p : ι × α, ∑ i, ∑ j, emb (c i) p * emb (c j) p := Finset.sum_comm
      _ = ∑ p : ι × α, (∑ i, emb (c i) p) ^ 2 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [sq, Finset.sum_mul_sum]
  rw [hswap]
  exact Finset.sum_nonneg fun p _ => sq_nonneg _

end CodeGeometry