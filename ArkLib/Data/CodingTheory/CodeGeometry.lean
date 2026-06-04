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

omit [Fintype ι] [DecidableEq ι] in
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
    rw [← Finset.mul_sum]; simp
  have h3 : (∑ a : α, (1/q) * (if v i = a then (1:ℝ) else 0)) = 1/q := by
    rw [← Finset.mul_sum]; simp
  have h4 : (∑ _a : α, (1/q)*(1/q)) = 1/q := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hqdef]
    field_simp
  rw [h1, h2, h3, h4]; ring

omit [DecidableEq ι] in
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

omit [DecidableEq ι] in
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

omit [DecidableEq ι] in
/-- **Shifted PSD.** The Gram-sum of the center-shifted embeddings
`y_i = x_{c i} − β·x_g` is nonnegative — the form of the Plotkin inequality
actually used in Johnson list-size arguments. -/
theorem sum_sum_shiftInner_nonneg {L : ℕ} (c : Fin L → ι → α) (g : ι → α) (β : ℝ) :
    0 ≤ ∑ i, ∑ j, (codeInner (c i) (c j)
      - β * codeInner (c i) g - β * codeInner (c j) g
      + β ^ 2 * codeInner g g) := by
  classical
  have hswap : (∑ i, ∑ j, (codeInner (c i) (c j)
      - β * codeInner (c i) g - β * codeInner (c j) g
      + β ^ 2 * codeInner g g))
      = ∑ p : ι × α, (∑ i, (emb (c i) p - β * emb g p)) ^ 2 := by
    calc (∑ i, ∑ j, (codeInner (c i) (c j)
        - β * codeInner (c i) g - β * codeInner (c j) g
        + β ^ 2 * codeInner g g))
        = ∑ i, ∑ j, ∑ p : ι × α,
            (emb (c i) p - β * emb g p) * (emb (c j) p - β * emb g p) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          simp only [codeInner, Finset.mul_sum, ← Finset.sum_sub_distrib,
            ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
      _ = ∑ i, ∑ p : ι × α, ∑ j,
            (emb (c i) p - β * emb g p) * (emb (c j) p - β * emb g p) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact Finset.sum_comm
      _ = ∑ p : ι × α, ∑ i, ∑ j,
            (emb (c i) p - β * emb g p) * (emb (c j) p - β * emb g p) :=
          Finset.sum_comm
      _ = ∑ p : ι × α, (∑ i, (emb (c i) p - β * emb g p)) ^ 2 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [sq, Finset.sum_mul_sum]
  rw [hswap]
  exact Finset.sum_nonneg fun p _ => sq_nonneg _

/-- **Abstract Gram counting.** If a symmetric-style Gram-sum is nonnegative,
the diagonal entries are at most `Dd`, and the off-diagonal entries are at most
`Do < 0`, then the family size obeys `(L−1)·(−Do) ≤ Dd` — the quadratic-in-`L`
cap of the Johnson list-size bound. -/
theorem card_le_of_gram_bounds {L : ℕ} (hL : 0 < L) (S : Fin L → Fin L → ℝ)
    {Dd Do : ℝ} (hpsd : 0 ≤ ∑ i, ∑ j, S i j)
    (hdiag : ∀ i, S i i ≤ Dd)
    (hoff : ∀ i j, i ≠ j → S i j ≤ Do) (hDo : Do < 0) :
    ((L : ℝ) - 1) * (-Do) ≤ Dd := by
  classical
  -- pick any i₀ and bound its row? No: use the full-sum bound.
  -- Σᵢⱼ S i j = Σᵢ S i i + Σᵢ Σ_{j≠i} S i j ≤ L·Dd + L(L−1)·Do
  have hdiag_sum : (∑ i, S i i) ≤ (L : ℝ) * Dd := by
    calc (∑ i, S i i) ≤ ∑ _i : Fin L, Dd := Finset.sum_le_sum fun i _ => hdiag i
      _ = (L : ℝ) * Dd := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  have hoff_sum : (∑ i, ∑ j ∈ Finset.univ.erase i, S i j)
      ≤ (L : ℝ) * ((L : ℝ) - 1) * Do := by
    have hrow : ∀ i : Fin L, (∑ j ∈ Finset.univ.erase i, S i j) ≤ ((L : ℝ) - 1) * Do := by
      intro i
      have hcard : (Finset.univ.erase i).card = L - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      calc (∑ j ∈ Finset.univ.erase i, S i j)
          ≤ ∑ _j ∈ Finset.univ.erase i, Do :=
            Finset.sum_le_sum fun j hj => hoff i j (Finset.ne_of_mem_erase hj).symm
        _ = ((L : ℝ) - 1) * Do := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]
            congr 1
            have : (1 : ℕ) ≤ L := hL
            push_cast [Nat.cast_sub this]
            ring
    calc (∑ i, ∑ j ∈ Finset.univ.erase i, S i j)
        ≤ ∑ _i : Fin L, ((L : ℝ) - 1) * Do := Finset.sum_le_sum fun i _ => hrow i
      _ = (L : ℝ) * (((L : ℝ) - 1) * Do) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (L : ℝ) * ((L : ℝ) - 1) * Do := by ring
  have hdecomp : (∑ i, ∑ j, S i j)
      = (∑ i, S i i) + ∑ i, ∑ j ∈ Finset.univ.erase i, S i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase Finset.univ (S i) (Finset.mem_univ i)]
  have hfull : (0 : ℝ) ≤ (L : ℝ) * Dd + (L : ℝ) * ((L : ℝ) - 1) * Do := by
    calc (0 : ℝ) ≤ ∑ i, ∑ j, S i j := hpsd
      _ = (∑ i, S i i) + ∑ i, ∑ j ∈ Finset.univ.erase i, S i j := hdecomp
      _ ≤ (L : ℝ) * Dd + (L : ℝ) * ((L : ℝ) - 1) * Do := add_le_add hdiag_sum hoff_sum
  -- rearrange: L(L−1)(−Do) ≤ L·Dd, divide by L > 0
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hDo_le : Do ≤ 0 := le_of_lt hDo
  nlinarith [hfull, hLpos, hDo_le]

end CodeGeometry
