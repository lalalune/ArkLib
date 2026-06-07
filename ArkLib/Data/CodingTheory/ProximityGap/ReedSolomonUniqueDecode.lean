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
/-- **Interpolant recovery (the `Y − p(X)` factorization), general degrees.**  Let `(A, B)` be a
Berlekamp–Welch / Polishchuk–Spielman interpolant for `(αᵢ, yᵢ)` — `A(αᵢ) + yᵢ·B(αᵢ) = 0` — with
`deg A < dA`, `deg B < dB`.  If a degree-`< k` polynomial `p` has `eval p` within `e` errors of `y`,
and the degrees fit under the agreement count (`dA ≤ n−e` and `k + dB ≤ n−e+1`), then `A + p·B = 0`.
Equivalently `Q(X,Y) = A(X) + Y·B(X)` satisfies `Q(X, p(X)) = 0`, so `Y − p(X)` divides `Q` — the
codeword `p = −A/B` is recovered.  This is the Welch–Berlekamp / Polishchuk–Spielman factorization
that turns interpolation existence into decoding (the locator degree `dB−1` may exceed the actual
error count `e`). -/
theorem interpolant_recovers {k dA dB e : ℕ} [NeZero k] {α : ι ↪ F} {y : ι → F} {A B p : F[X]}
    (hA : A ∈ Polynomial.degreeLT F dA) (hB : B ∈ Polynomial.degreeLT F dB)
    (hp : p ∈ Polynomial.degreeLT F k)
    (hkey : ∀ i, A.eval (α i) + y i * B.eval (α i) = 0)
    (herr : (Finset.univ.filter (fun i => y i ≠ p.eval (α i))).card ≤ e)
    (he : e < Fintype.card ι)
    (hdA : dA ≤ Fintype.card ι - e) (hdB : k + dB ≤ Fintype.card ι - e + 1) :
    A + p * B = 0 := by
  classical
  by_contra hne
  have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  -- degree bounds from the `degreeLT` memberships
  have hdp : p.natDegree ≤ k - 1 := by
    rcases eq_or_ne p 0 with rfl | h; · simp
    · have : p.natDegree < k := (natDegree_lt_iff_degree_lt h).mpr (mem_degreeLT.mp hp); omega
  have hdBn : B.natDegree ≤ dB - 1 := by
    rcases eq_or_ne B 0 with rfl | h; · simp
    · have : B.natDegree < dB := (natDegree_lt_iff_degree_lt h).mpr (mem_degreeLT.mp hB)
      omega
  have hdAn : A.natDegree ≤ dA - 1 := by
    rcases eq_or_ne A 0 with rfl | h; · simp
    · have : A.natDegree < dA := (natDegree_lt_iff_degree_lt h).mpr (mem_degreeLT.mp hA)
      omega
  -- `deg (A + p·B) ≤ max(dA−1, (k−1)+(dB−1)) ≤ n − e − 1`
  have hdeg : (A + p * B).natDegree ≤ Fintype.card ι - e - 1 := by
    have hA' : A.natDegree ≤ Fintype.card ι - e - 1 := by omega
    have hpB' : (p * B).natDegree ≤ Fintype.card ι - e - 1 := by
      rcases eq_or_ne B 0 with rfl | hB0
      · simp
      rcases eq_or_ne p 0 with rfl | hp0
      · simp
      · rw [natDegree_mul hp0 hB0]
        have hBnd : B.natDegree < dB := (natDegree_lt_iff_degree_lt hB0).mpr (mem_degreeLT.mp hB)
        omega
    exact le_trans (natDegree_add_le _ _) (max_le hA' hpB')
  -- `A + p·B` vanishes at the `≥ n − e` agreement coordinates
  have hroot : ∀ i, y i = p.eval (α i) → (A + p * B).eval (α i) = 0 := by
    intro i hi
    rw [eval_add, eval_mul, ← hi, hkey i]
  have hag_card : Fintype.card ι - e
      ≤ (Finset.univ.filter (fun i => y i = p.eval (α i))).card := by
    have hco : (Finset.univ.filter (fun i => y i = p.eval (α i)))
        = (Finset.univ.filter (fun i => y i ≠ p.eval (α i)))ᶜ := by ext i; simp
    rw [hco, Finset.card_compl]; omega
  have hsub : (Finset.univ.filter (fun i => y i = p.eval (α i))).map α
      ⊆ (A + p * B).roots.toFinset := by
    intro x hx
    rw [Finset.mem_map] at hx; obtain ⟨i, hi, rfl⟩ := hx
    rw [Multiset.mem_toFinset, mem_roots hne, IsRoot.def]
    exact hroot i (Finset.mem_filter.mp hi).2
  have hle : Fintype.card ι - e ≤ (A + p * B).natDegree := by
    calc Fintype.card ι - e
        ≤ (Finset.univ.filter (fun i => y i = p.eval (α i))).card := hag_card
      _ = ((Finset.univ.filter (fun i => y i = p.eval (α i))).map α).card := (Finset.card_map _).symm
      _ ≤ (A + p * B).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (A + p * B).roots := Multiset.toFinset_card_le _
      _ ≤ (A + p * B).natDegree := card_roots' _
  omega

open Polynomial in
/-- **Bivariate root extraction (Sudan / Guruswami–Sudan factorization).**  Let
`Q(X,Y) = ∑ⱼ Qⱼ(X)·Yʲ` be a bidegree-`(≤ dX, ≤ dZ)` bivariate polynomial vanishing at every point
`(αᵢ, yᵢ)`.  If a degree-`< k` polynomial `p` has `eval p` within `e` errors of `y`, and the agreement
exceeds the curve degree (`dX + dZ·(k−1) < n − e`), then `∑ⱼ Qⱼ·pʲ = 0` — i.e. `Q(X, p(X)) = 0`, so
`Y − p(X)` divides `Q(X, Y)` and `p` is a `Y`-root of `Q`.  This is the list-decoding recovery: every
close codeword is a factor of the interpolant, so the list size is bounded by `deg_Y Q ≤ dZ`.  The
factorization half of the Polishchuk–Spielman / BCIKS20 / Sudan bivariate argument. -/
theorem bivariate_root_of_close {k dX dZ e : ℕ} [NeZero k] {α : ι ↪ F} {y : ι → F}
    {Q : Fin (dZ + 1) → F[X]} {p : F[X]}
    (hQ : ∀ j, Q j ∈ Polynomial.degreeLT F (dX + 1)) (hp : p ∈ Polynomial.degreeLT F k)
    (hint : ∀ i, ∑ j : Fin (dZ + 1), (Q j).eval (α i) * (y i) ^ (j : ℕ) = 0)
    (herr : (Finset.univ.filter (fun i => y i ≠ p.eval (α i))).card ≤ e)
    (he : e < Fintype.card ι) (hdeg : dX + dZ * (k - 1) < Fintype.card ι - e) :
    ∑ j : Fin (dZ + 1), Q j * p ^ (j : ℕ) = 0 := by
  classical
  set R := ∑ j : Fin (dZ + 1), Q j * p ^ (j : ℕ) with hR
  by_contra hRne
  have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hpd : p.natDegree ≤ k - 1 := by
    rcases eq_or_ne p 0 with rfl | h; · simp
    · have : p.natDegree < k := (natDegree_lt_iff_degree_lt h).mpr (mem_degreeLT.mp hp); omega
  -- each term has degree `≤ dX + dZ·(k−1)`
  have hterm : ∀ j : Fin (dZ + 1), (Q j * p ^ (j : ℕ)).natDegree ≤ dX + dZ * (k - 1) := by
    intro j
    have hQd : (Q j).natDegree ≤ dX := by
      rcases eq_or_ne (Q j) 0 with h | h; · simp [h]
      · have : (Q j).natDegree < dX + 1 := (natDegree_lt_iff_degree_lt h).mpr (mem_degreeLT.mp (hQ j))
        omega
    calc (Q j * p ^ (j : ℕ)).natDegree
        ≤ (Q j).natDegree + (p ^ (j : ℕ)).natDegree := natDegree_mul_le
      _ ≤ dX + (j : ℕ) * (k - 1) := by
          have := natDegree_pow_le (p := p) (n := (j : ℕ)); nlinarith [hpd, hQd, this]
      _ ≤ dX + dZ * (k - 1) := by
          have : (j : ℕ) ≤ dZ := by omega
          exact Nat.add_le_add_left (Nat.mul_le_mul_right _ this) _
  have hRdeg : R.natDegree ≤ dX + dZ * (k - 1) :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => hterm j)
  -- `R` vanishes on the `≥ n − e` agreement coordinates
  have hroot : ∀ i, y i = p.eval (α i) → R.eval (α i) = 0 := by
    intro i hi
    rw [hR, eval_finset_sum, ← hint i]
    exact Finset.sum_congr rfl fun j _ => by rw [eval_mul, eval_pow, hi]
  have hag_card : Fintype.card ι - e
      ≤ (Finset.univ.filter (fun i => y i = p.eval (α i))).card := by
    have hco : (Finset.univ.filter (fun i => y i = p.eval (α i)))
        = (Finset.univ.filter (fun i => y i ≠ p.eval (α i)))ᶜ := by ext i; simp
    rw [hco, Finset.card_compl]; omega
  have hsub : (Finset.univ.filter (fun i => y i = p.eval (α i))).map α ⊆ R.roots.toFinset := by
    intro w hw
    rw [Finset.mem_map] at hw; obtain ⟨i, hi, rfl⟩ := hw
    rw [Multiset.mem_toFinset, mem_roots hRne, IsRoot.def]
    exact hroot i (Finset.mem_filter.mp hi).2
  have hle : Fintype.card ι - e ≤ R.natDegree := by
    calc Fintype.card ι - e
        ≤ (Finset.univ.filter (fun i => y i = p.eval (α i))).card := hag_card
      _ = ((Finset.univ.filter (fun i => y i = p.eval (α i))).map α).card := (Finset.card_map _).symm
      _ ≤ R.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card R.roots := Multiset.toFinset_card_le _
      _ ≤ R.natDegree := card_roots' _
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
theorem jointAgreement_of_common_locator {α : ι ↪ F} {e : ℕ}
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
        rcases le_total e (Fintype.card ι) with h | h
        · rw [Nat.cast_sub h]
        · have : ((Fintype.card ι - e : ℕ) : ℝ) = 0 := by
            rw [Nat.sub_eq_zero_of_le h]; simp
          rw [this]
          have : (Fintype.card ι : ℝ) ≤ e := by exact_mod_cast h
          linarith
      exact le_trans hle (by exact_mod_cast hScard)
    have hgoal : ((1 - δ : ℝ≥0) : ℝ) * Fintype.card ι ≤ (S.card : ℝ) := by
      rw [NNReal.coe_sub hδ1]; push_cast; nlinarith [hδ, hSr]
    have : ((1 - δ : ℝ≥0) * Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) := by
      rw [← NNReal.coe_le_coe]; push_cast; exact hgoal
    exact_mod_cast this
  · intro j
    fin_cases j
    · refine ⟨Submodule.mem_map.mpr ⟨g₀, hg₀, rfl⟩, ?_⟩
      intro i hi
      simpa [ReedSolomon.evalOnPoints] using (h₀ i hi).symm
    · refine ⟨Submodule.mem_map.mpr ⟨g₁, hg₁, rfl⟩, ?_⟩
      intro i hi
      simpa [ReedSolomon.evalOnPoints] using (h₁ i hi).symm

/-- **Exact-radius shared-locator corollary.**  The shared-locator theorem applies at the natural
boundary radius `δ = e / |ι|` whenever `e ≤ |ι|` and the evaluation domain is nonempty. This is the
same conditional BCIKS20 reconstruction as `reedSolomon_jointAgreement_of_shared_locator`, with the
radius side conditions discharged. -/
theorem reedSolomon_jointAgreement_of_shared_locator_exact [Fintype F]
    {α : ι ↪ F} {k e : ℕ} [NeZero k] {u₀ u₁ : ι → F} {E g₀ g₁ : F[X]}
    (hE0 : E ≠ 0) (hEdeg : E.natDegree ≤ e)
    (hg₀ : g₀ ∈ Polynomial.degreeLT F k) (hg₁ : g₁ ∈ Polynomial.degreeLT F k)
    (hkey₀ : ∀ i, E.eval (α i) * u₀ i = (E * g₀).eval (α i))
    (hkey₁ : ∀ i, E.eval (α i) * u₁ i = (E * g₁).eval (α i))
    (hn : 0 < Fintype.card ι) (he : e ≤ Fintype.card ι) :
    Code.jointAgreement (↑(ReedSolomon.code α k) : Set (ι → F))
      ((e : ℝ≥0) / (Fintype.card ι : ℝ≥0))
      (![u₀, u₁] : Fin 2 → ι → F) := by
  refine reedSolomon_jointAgreement_of_shared_locator
    hE0 hEdeg hg₀ hg₁ hkey₀ hkey₁
    ((e : ℝ≥0) / (Fintype.card ι : ℝ≥0)) ?_ ?_
  · rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast he
  · rw [NNReal.coe_div]
    norm_num
    rw [div_mul_cancel₀ _ (by exact_mod_cast hn.ne')]

#print axioms ReedSolomon.jointAgreement_of_common_locator
#print axioms ReedSolomon.reedSolomon_jointAgreement_of_shared_locator
#print axioms ReedSolomon.reedSolomon_jointAgreement_of_shared_locator_exact

end ReedSolomon
