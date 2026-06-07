/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.TwoLineExtraction
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Polynomial.UnivariateAgreement

/-!
# Reed–Solomon unique decoding (concrete instantiation)

Instantiating the abstract linear-code unique-decoding theorems
(`ProximityGap.codeword_eq_of_agree_minDist`, `ProximityGap.eq_of_close_to_common`,
`ProximityGap.closeCodewords_subsingleton`) at the concrete Reed–Solomon minimum distance
`minDist(RS[n,k]) = |ι| − k + 1` (`ReedSolomon.minDist_eq'`):

* `ReedSolomon.code_eq_of_agree` — two degree-`< k` RS codewords agreeing on `≥ k` evaluation points
  are equal (a degree-`< k` polynomial is pinned by `k` evaluations);
* `ReedSolomon.unique_decode` — the RS ball of radius `< (|ι|−k+1)/2` contains at most one codeword.

These are fully self-contained named Reed–Solomon results with no abstract hypotheses.
-/

namespace ReedSolomon

open ProximityGap
open scoped Polynomial NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F] [DecidableEq F]

/-- **Reed–Solomon unique decoding (agreement form).**  Two RS codewords of degree `< k` that agree
on more than `k − 1` evaluation points are equal.  (Instantiates the abstract unique-decoding
theorem with `minDist(RS) = |ι| − k + 1`.) -/
theorem code_eq_of_agree {α : ι ↪ F} {k : ℕ} [NeZero k] (hk : k ≤ Fintype.card ι)
    {c c' : ι → F} (hc : c ∈ ReedSolomon.code α k) (hc' : c' ∈ ReedSolomon.code α k)
    {S : Finset ι} (hagree : ∀ i ∈ S, c i = c' i) (hS : k - 1 < S.card) :
    c = c' := by
  refine codeword_eq_of_agree_minDist (ReedSolomon.code α k) hc hc' hagree ?_
  rw [minDist_eq' hk]
  omega

/-- **Reed–Solomon unique decoding (ball form).**  The RS ball of radius `e` with `2e < |ι| − k + 1`
contains at most one codeword: two RS codewords within distance `e` of a common word coincide. -/
theorem unique_decode {α : ι ↪ F} {k : ℕ} [NeZero k] (hk : k ≤ Fintype.card ι)
    {f c c' : ι → F} {e : ℕ}
    (hc : c ∈ ReedSolomon.code α k) (hc' : c' ∈ ReedSolomon.code α k)
    (hd : hammingDist f c ≤ e) (hd' : hammingDist f c' ≤ e)
    (he : 2 * e < Fintype.card ι - k + 1) :
    c = c' := by
  refine eq_of_close_to_common (ReedSolomon.code α k) hc hc' hd hd' ?_
  rw [minDist_eq' hk]
  exact he

/-- **Reed–Solomon evaluation injectivity.**  A degree-`< k` polynomial is determined by its
Reed–Solomon codeword: if two polynomials of degree `< k` evaluate to the same word on the `≥ k`
evaluation points, they are equal.  (A nonzero difference of degree `< k` would have `≥ |ι| ≥ k`
roots — impossible.)  This is the polynomial↔codeword bijection underlying the polynomial-method
proximity-gap arguments. -/
theorem evalOnPoints_injOn_degreeLT [Fintype F] {α : ι ↪ F} {k : ℕ} [NeZero k]
    (hk : k ≤ Fintype.card ι)
    {p q : F[X]} (hp : p ∈ Polynomial.degreeLT F k) (hq : q ∈ Polynomial.degreeLT F k)
    (heq : ReedSolomon.evalOnPoints α p = ReedSolomon.evalOnPoints α q) : p = q := by
  by_contra hne
  have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  -- both polynomials have `natDegree < k`, hence `≤ k − 1`
  have hdeg : ∀ {r : F[X]}, r ∈ Polynomial.degreeLT F k → r.natDegree ≤ k - 1 := by
    intro r hr
    rcases eq_or_ne r 0 with rfl | hr0
    · simpa using Nat.le_sub_one_of_lt hkpos
    · have : r.natDegree < k := (Polynomial.natDegree_lt_iff_degree_lt hr0).mpr
        (Polynomial.mem_degreeLT.mp hr)
      omega
  -- the agreement set over `F` contains the `|ι|` distinct evaluation points
  have himg : Finset.univ.map α ⊆ Finset.univ.filter (fun x : F => p.eval x = q.eval x) := by
    intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨x, _, rfl⟩ := hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrFun heq x⟩
  have hcard2 : Fintype.card ι ≤ (Finset.univ.filter (fun x : F => p.eval x = q.eval x)).card := by
    calc Fintype.card ι = (Finset.univ.map α).card := by rw [Finset.card_map, Finset.card_univ]
      _ ≤ _ := Finset.card_le_card himg
  -- but two distinct degree-`≤ k−1` polynomials agree at `≤ k − 1` points
  have hcard := Polynomial.card_agree_le_of_ne (hdeg hp) (hdeg hq) hne
  omega

open Polynomial in
/-- **Berlekamp–Welch key-equation existence.**  If a received word `y` is within `e` Hamming
errors of the Reed–Solomon codeword `eval f` (`f` of degree `< k`), then the Berlekamp–Welch key
equation `E(αᵢ)·yᵢ = N(αᵢ)` has a solution with `E ≠ 0`, `deg E ≤ e`, `deg N < k + e`.  Witnessed
by the **error-locator** `E := ∏_{error i}(X − αᵢ)` (which vanishes exactly at the error positions)
and `N := E · f`.  This is the algebraic heart of unique decoding and the entry point to the
bivariate proximity-gap argument. -/
theorem berlekamp_welch_exists {α : ι ↪ F} {k e : ℕ} [NeZero k]
    {y : ι → F} {f : F[X]} (hf : f ∈ Polynomial.degreeLT F k)
    (herr : (Finset.univ.filter (fun i => y i ≠ f.eval (α i))).card ≤ e) :
    ∃ E N : F[X], E ≠ 0 ∧ E.natDegree ≤ e ∧ N.natDegree < k + e ∧
      ∀ i, E.eval (α i) * y i = N.eval (α i) := by
  classical
  set errs := Finset.univ.filter (fun i => y i ≠ f.eval (α i)) with hes
  set E : F[X] := ∏ i ∈ errs, (X - C (α i)) with hE
  have hEne : E ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero (α i)
  -- `deg E = |errs| ≤ e`
  have hEdeg : E.natDegree ≤ e := by
    rw [hE, natDegree_prod _ _ fun i _ => X_sub_C_ne_zero (α i)]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
    exact herr
  refine ⟨E, E * f, hEne, hEdeg, ?_, ?_⟩
  · -- `deg (E·f) < k + e`
    have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
    rcases eq_or_ne f 0 with rfl | hf0
    · rw [mul_zero, natDegree_zero]; omega
    · have hfdeg : f.natDegree < k := (natDegree_lt_iff_degree_lt hf0).mpr (mem_degreeLT.mp hf)
      rw [natDegree_mul hEne hf0]
      omega
  · -- key equation
    intro i
    by_cases hi : i ∈ errs
    · have hEz : E.eval (α i) = 0 := by
        rw [hE, eval_prod]
        exact Finset.prod_eq_zero hi (by simp)
      simp [hEz, eval_mul]
    · have hyc : y i = f.eval (α i) := by
        by_contra h; exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      rw [eval_mul, hyc]

open Polynomial in
/-- **Berlekamp–Welch recovery.**  In the unique-decoding regime `k + 2e < n`, any solution
`(E, N)` of the key equation (with `E ≠ 0`, `deg E ≤ e`, `deg N < k + e`) for a word `y` that is
`e`-close to the codeword `eval f` satisfies `N = E · f`.  Hence `f = N / E` is recovered.  Proof:
`R := N − E·f` has degree `< k + e` yet vanishes at the `≥ n − e` agreement coordinates, so
`n − e ≤ deg R < k + e` would give `n < k + 2e` — contradiction; thus `R = 0`. -/
theorem berlekamp_welch_recovers {α : ι ↪ F} {k e : ℕ} [NeZero k]
    {y : ι → F} {f E N : F[X]} (hf : f ∈ Polynomial.degreeLT F k) (hE0 : E ≠ 0)
    (hEdeg : E.natDegree ≤ e) (hNdeg : N.natDegree < k + e)
    (hkey : ∀ i, E.eval (α i) * y i = N.eval (α i))
    (herr : (Finset.univ.filter (fun i => y i ≠ f.eval (α i))).card ≤ e)
    (hn : k + 2 * e < Fintype.card ι) :
    N = E * f := by
  classical
  by_contra hne
  have hR0 : N - E * f ≠ 0 := sub_ne_zero.mpr hne
  have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hfdeg : f.natDegree ≤ k - 1 := by
    rcases eq_or_ne f 0 with rfl | hf0
    · simp
    · have : f.natDegree < k := (natDegree_lt_iff_degree_lt hf0).mpr (mem_degreeLT.mp hf); omega
  -- `deg (N − E·f) < k + e`
  have hRdeg : (N - E * f).natDegree < k + e := by
    have h1 : (E * f).natDegree ≤ k + e - 1 := by
      rcases eq_or_ne f 0 with rfl | hf0
      · simp
      · rw [natDegree_mul hE0 hf0]; omega
    calc (N - E * f).natDegree ≤ max N.natDegree (E * f).natDegree := natDegree_sub_le _ _
      _ < k + e := by omega
  -- `R` vanishes on the agreement set
  have hroot : ∀ i, y i = f.eval (α i) → (N - E * f).eval (α i) = 0 := by
    intro i hi
    rw [eval_sub, eval_mul, ← hkey i, hi]; ring
  set agree := Finset.univ.filter (fun i => y i = f.eval (α i)) with hag
  have hagree_card : Fintype.card ι - e ≤ agree.card := by
    have hco : agree = (Finset.univ.filter (fun i => y i ≠ f.eval (α i)))ᶜ := by
      ext i; simp [hag, not_not]
    rw [hco, Finset.card_compl]; omega
  have hsub : agree.map α ⊆ (N - E * f).roots.toFinset := by
    intro x hx
    rw [Finset.mem_map] at hx; obtain ⟨i, hi, rfl⟩ := hx
    rw [Multiset.mem_toFinset, mem_roots hR0, IsRoot.def]
    exact hroot i (Finset.mem_filter.mp hi).2
  have hle : agree.card ≤ (N - E * f).natDegree := by
    calc agree.card = (agree.map α).card := (Finset.card_map _).symm
      _ ≤ (N - E * f).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (N - E * f).roots := Multiset.toFinset_card_le _
      _ ≤ (N - E * f).natDegree := card_roots' _
  omega

open Polynomial in
/-- **Common-locator full-radius joint agreement (BCIKS20 bivariate-lift core).**  Suppose a single
error locator `E ≠ 0` (degree `≤ e`) and codeword polynomials `g₀, g₁` of degree `< k` satisfy the
two key equations `E(αᵢ)·u₀ᵢ = (E·g₀)(αᵢ)` and `E(αᵢ)·u₁ᵢ = (E·g₁)(αᵢ)` on every coordinate.  Then
on the set `{i : E(αᵢ) ≠ 0}` — of size `≥ n − e` — **both** `u₀` and `u₁` agree with the codewords
`eval g₀`, `eval g₁`.  This is exactly the mechanism that achieves the *full* radius `e/n` (not the
two-line `2δ`): the **shared** locator forces a **common** agreement set, eliminating the factor-2
loss.  (The remaining BCIKS20 ingredient is the bivariate existence of such a shared `(E, g₀, g₁)`
from the many-close-scalars hypothesis.) -/
theorem jointAgreement_of_common_locator {α : ι ↪ F} {k e : ℕ}
    {u₀ u₁ : ι → F} {E g₀ g₁ : F[X]}
    (hE0 : E ≠ 0) (hEdeg : E.natDegree ≤ e)
    (hkey₀ : ∀ i, E.eval (α i) * u₀ i = (E * g₀).eval (α i))
    (hkey₁ : ∀ i, E.eval (α i) * u₁ i = (E * g₁).eval (α i)) :
    ∃ S : Finset ι, Fintype.card ι - e ≤ S.card ∧
      (∀ i ∈ S, u₀ i = g₀.eval (α i)) ∧ (∀ i ∈ S, u₁ i = g₁.eval (α i)) := by
  classical
  refine ⟨Finset.univ.filter (fun i => E.eval (α i) ≠ 0), ?_, ?_, ?_⟩
  · -- `|{E(αᵢ) ≠ 0}| = n − |{E(αᵢ) = 0}| ≥ n − e`
    have hroots : (Finset.univ.filter (fun i => E.eval (α i) = 0)).card ≤ e := by
      have hsub : (Finset.univ.filter (fun i => E.eval (α i) = 0)).map α ⊆ E.roots.toFinset := by
        intro x hx
        rw [Finset.mem_map] at hx; obtain ⟨i, hi, rfl⟩ := hx
        rw [Multiset.mem_toFinset, mem_roots hE0, IsRoot.def]
        exact (Finset.mem_filter.mp hi).2
      calc (Finset.univ.filter (fun i => E.eval (α i) = 0)).card
          = ((Finset.univ.filter (fun i => E.eval (α i) = 0)).map α).card := (Finset.card_map _).symm
        _ ≤ E.roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ Multiset.card E.roots := Multiset.toFinset_card_le _
        _ ≤ E.natDegree := card_roots' _
        _ ≤ e := hEdeg
    have hcompl : (Finset.univ.filter (fun i => E.eval (α i) ≠ 0))
        = (Finset.univ.filter (fun i => E.eval (α i) = 0))ᶜ := by ext i; simp
    rw [hcompl, Finset.card_compl]; omega
  · intro i hi
    have hEne : E.eval (α i) ≠ 0 := (Finset.mem_filter.mp hi).2
    have h := hkey₀ i; rw [eval_mul] at h
    exact mul_left_cancel₀ hEne h
  · intro i hi
    have hEne : E.eval (α i) ≠ 0 := (Finset.mem_filter.mp hi).2
    have h := hkey₁ i; rw [eval_mul] at h
    exact mul_left_cancel₀ hEne h

open Polynomial in
/-- **BCIKS20 exact-radius proximity gap for Reed–Solomon, conditional on the shared locator.**
If the affine-line stack `(u₀, u₁)` admits a shared Berlekamp–Welch locator `E` with codeword
polynomials `g₀, g₁` (degree `< k`) solving both key equations, then the pair is jointly
`δ`-close to `RS[k]` at the *full* radius `δ ≥ e/n` — `Code.jointAgreement` with the common
agreement set `{E(αᵢ) ≠ 0}`.

This packages building blocks #1–#4a; the **only** remaining ingredient for the unconditional
BCIKS20 exact-radius theorem is the bivariate existence of such a shared `(E, g₀, g₁)` from the
many-close-scalars hypothesis (the bivariate-interpolation core). -/
theorem reedSolomon_jointAgreement_of_shared_locator [Fintype F]
    {α : ι ↪ F} {k e : ℕ} [NeZero k] {u₀ u₁ : ι → F} {E g₀ g₁ : F[X]}
    (hE0 : E ≠ 0) (hEdeg : E.natDegree ≤ e)
    (hg₀ : g₀ ∈ Polynomial.degreeLT F k) (hg₁ : g₁ ∈ Polynomial.degreeLT F k)
    (hkey₀ : ∀ i, E.eval (α i) * u₀ i = (E * g₀).eval (α i))
    (hkey₁ : ∀ i, E.eval (α i) * u₁ i = (E * g₁).eval (α i))
    (δ : ℝ≥0) (hδ1 : δ ≤ 1) (hδ : (e : ℝ) ≤ δ * Fintype.card ι) :
    Code.jointAgreement (↑(ReedSolomon.code α k) : Set (ι → F)) δ
      (![u₀, u₁] : Fin 2 → ι → F) := by
  classical
  obtain ⟨S, hScard, h₀, h₁⟩ := jointAgreement_of_common_locator hE0 hEdeg hkey₀ hkey₁
  refine ⟨S, ?_, ![ReedSolomon.evalOnPoints α g₀, ReedSolomon.evalOnPoints α g₁], ?_⟩
  · -- `(1 − δ)·n ≤ |S|`, since `|S| ≥ n − e` and `e ≤ δ·n`
    have hSr : ((Fintype.card ι : ℝ) - e) ≤ (S.card : ℝ) := by
      have := hScard
      have hle : (Fintype.card ι : ℝ) - e ≤ ((Fintype.card ι - e : ℕ) : ℝ) := by
        rcases le_or_lt e (Fintype.card ι) with h | h
        · rw [Nat.cast_sub h]
        · simp only [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]; linarith [Nat.cast_le.mpr h.le (α := ℝ)]
      exact le_trans hle (by exact_mod_cast hScard)
    have hgoal : ((1 - δ : ℝ≥0) : ℝ) * Fintype.card ι ≤ (S.card : ℝ) := by
      rw [NNReal.coe_sub hδ1]; push_cast; nlinarith [hδ, hSr]
    have : ((1 - δ : ℝ≥0) * Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) := by
      rw [← NNReal.coe_le_coe]; push_cast; exact hgoal
    exact_mod_cast this
  · intro j
    fin_cases j
    · refine ⟨Submodule.apply_mem_map _ hg₀, ?_⟩
      intro i hi
      simpa [ReedSolomon.evalOnPoints] using (h₀ i hi).symm
    · refine ⟨Submodule.apply_mem_map _ hg₁, ?_⟩
      intro i hi
      simpa [ReedSolomon.evalOnPoints] using (h₁ i hi).symm

end ReedSolomon
