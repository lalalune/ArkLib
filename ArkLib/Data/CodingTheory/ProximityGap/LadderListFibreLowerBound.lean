/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26AlignmentSupply

/-!
# The fibre-law supply side: ladder lists attain the subset-sum fibre (#389)

The subset-sum fibre law (the exact sub-Johnson list-size conjecture, #389; probes
12/12 exact at three scales including the multi-tower crossover) states that the
maximal sub-Johnson list size is `max N_fib(s,r)`, attained by ladder words.  This file
proves the **attained (lower) half**:

> **`ladder_list_ge_fibre`** — for the ladder word `w = x^{rm} + λ·x^{(r−1)m}` on the
> smooth `s·m`-point domain, the number of `rsCode` codewords (dimension `k`,
> `(r−2)m < k ≤ rm`) with agreement `≥ rm` with `w` is at least the subset-sum fibre
> count `#{T ⊆ μ_s : |T| = r, −∑T = λ}`.

The injection sends `T` to the `badline_pointwise_agreement` interpolant `q_T`, which
agrees with `w` on the `rm`-point fibre union of `T`.  **Injectivity is a root count**:
if `q_T = q_{T'}` for `T ≠ T'` in the same fibre, then
`D := X^{rm} + λX^{(r−1)m} − q` vanishes on the fibre union of `T ∪ T'` — at least
`(r+1)·m > rm ≥ deg D` distinct points — so `D = 0`; but the `X^{rm}`-coefficient of `D`
is `1` (both other terms have lower degree), a contradiction.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal
open ProximityGap.SpikeFloor ProximityGap ArkLib.ProximityGap.KKH26

namespace ProximityGap.Ownership

variable {p : ℕ} [Fact p.Prime]

/-- Power injectivity below the order (local copy; the supply file's is private). -/
private lemma pow_inj_llf {F : Type*} [Field F] {h : F} (h0 : h ≠ 0) {N : ℕ}
    (hN : orderOf h = N) :
    ∀ i, i < N → ∀ j, j < N → h ^ i = h ^ j → i = j := by
  have main : ∀ i j, i ≤ j → j < N → h ^ i = h ^ j → i = j := by
    intro i j hij hj heq
    have hadd : i + (j - i) = j := by omega
    have h2 : h ^ i * h ^ (j - i) = h ^ i * 1 := by
      rw [mul_one, ← pow_add, hadd, heq]
    have h3 : h ^ (j - i) = 1 := mul_left_cancel₀ (pow_ne_zero i h0) h2
    have h4 : N ∣ j - i := hN ▸ orderOf_dvd_of_pow_eq_one h3
    have h5 : j - i = 0 :=
      Nat.eq_zero_of_dvd_of_lt h4 (lt_of_le_of_lt (Nat.sub_le j i) hj)
    omega
  intro i hi j hj heq
  rcases le_total i j with hle | hle
  · exact main i j hle hj heq
  · exact (main j i hle hi heq.symm).symm

private lemma g_ne_zero_llf {g : ZMod p} {N : ℕ} (hN : 1 ≤ N) (hg : orderOf g = N) :
    g ≠ 0 := by
  rintro rfl
  have h1 : (0 : ZMod p) ^ N = 1 := by rw [← hg]; exact pow_orderOf_eq_one 0
  rw [zero_pow (by omega : N ≠ 0)] at h1
  exact absurd h1 zero_ne_one


open Classical in
/-- **The fibre-law supply side**: the ladder word's list at agreement `rm` is at least
the subset-sum fibre count. -/
theorem ladder_list_ge_fibre
    {s m : ℕ} (hs : 1 ≤ s) (hm : 1 ≤ m) {n : ℕ} [NeZero n] (hn : n = s * m)
    {g : ZMod p} (hg : orderOf g = n) {r k : ℕ} (hr2 : 2 ≤ r)
    (hk1 : (r - 2) * m < k) (hk2 : k ≤ r * m) (lam : ZMod p) :
    ((((Finset.range s).image (fun j => (g ^ m) ^ j)).powersetCard r).filter
        (fun T => -(∑ a ∈ T, a) = lam)).card
      ≤ (Finset.univ.filter (fun c : Fin n → ZMod p =>
          c ∈ (rsCode (smoothDom g n hg) k : Submodule (ZMod p) (Fin n → ZMod p)) ∧
          r * m ≤ (Finset.univ.filter (fun i : Fin n =>
            c i = (g ^ (i : ℕ)) ^ (r * m) + lam * (g ^ (i : ℕ)) ^ ((r - 1) * m))).card)).card := by
  classical
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  set G : Finset (ZMod p) := (Finset.range s).image (fun j => (g ^ m) ^ j) with hG
  -- the interpolant data for an r-subset of G
  have hbad : ∀ T ∈ (G.powersetCard r).filter (fun T => -(∑ a ∈ T, a) = lam),
      ∃ q : Polynomial (ZMod p), q.natDegree ≤ (r - 2) * m ∧
        ∀ x : ZMod p, x ^ m ∈ T →
          x ^ (r * m) + lam * x ^ ((r - 1) * m) = q.eval x := by
    intro T hT
    obtain ⟨hTmem, hTlam⟩ := Finset.mem_filter.mp hT
    have hTcard : T.card = r := (Finset.mem_powersetCard.mp hTmem).2
    obtain ⟨q, hqdeg, hq⟩ := badline_pointwise_agreement (p := p) hm T
      (by omega : 2 ≤ T.card)
    rw [hTcard] at hqdeg
    refine ⟨q, hqdeg, fun x hx => ?_⟩
    have h := hq x hx
    rw [hTcard, hTlam] at h
    exact h
  choose qf hqdeg hqag using hbad
  -- the codeword map
  set f : Finset (ZMod p) → (Fin n → ZMod p) := fun T =>
    if h : T ∈ (G.powersetCard r).filter (fun T => -(∑ a ∈ T, a) = lam)
    then (fun i => (qf T h).eval ((smoothDom g n hg) i)) else 0 with hf
  -- index-level fibre of a subset of G, and its domain image cardinality
  have hfibcard : ∀ U : Finset (ZMod p), U ⊆ G →
      ((Finset.univ.filter (fun i : Fin n => (g ^ (i : ℕ)) ^ m ∈ U)).image
        (fun i : Fin n => g ^ (i : ℕ))).card = m * U.card := by
    intro U hU
    have hinj : Set.InjOn (fun i : Fin n => g ^ (i : ℕ))
        ↑(Finset.univ.filter (fun i : Fin n => (g ^ (i : ℕ)) ^ m ∈ U)) := by
      intro a _ b _ hab
      exact Fin.ext (pow_inj_llf (g_ne_zero_llf hn1 hg) hg a a.isLt b b.isLt hab)
    rw [Finset.card_image_of_injOn hinj]
    -- bridge index-level filter to the domain-level fiber_count
    have hbij : (Finset.univ.filter (fun i : Fin n => (g ^ (i : ℕ)) ^ m ∈ U)).card
        = (((Finset.range (s * m)).image (fun i => g ^ i)).filter
            (fun x => x ^ m ∈ U)).card := by
      refine Finset.card_bij (fun i _ => g ^ (i : ℕ)) ?_ ?_ ?_
      · intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
          ⟨(i : ℕ), Finset.mem_range.mpr (hn ▸ i.isLt), rfl⟩,
          (Finset.mem_filter.mp hi).2⟩
      · intro a ha b hb hab
        exact Fin.ext (pow_inj_llf (g_ne_zero_llf hn1 hg) hg a a.isLt b b.isLt hab)
      · intro x hx
        obtain ⟨hmem, hpm⟩ := Finset.mem_filter.mp hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hmem
        exact ⟨⟨i, hn ▸ Finset.mem_range.mp hi⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpm⟩, rfl⟩
    rw [hbij, fiber_count hm hs (hn ▸ hg) U hU]
  -- membership of the image
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro T hT
    have hfT : f T = fun i => (qf T hT).eval ((smoothDom g n hg) i) := dif_pos hT
    rw [hfT]
    obtain ⟨hTmem, hTlam⟩ := Finset.mem_filter.mp hT
    have hTsub : T ⊆ G := (Finset.mem_powersetCard.mp hTmem).1
    have hTcard : T.card = r := (Finset.mem_powersetCard.mp hTmem).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨qf T hT, ?_, rfl⟩, ?_⟩
    · -- degree < k
      calc (qf T hT).degree ≤ ((qf T hT).natDegree : WithBot ℕ) :=
            Polynomial.degree_le_natDegree
      _ ≤ (((r - 2) * m : ℕ) : WithBot ℕ) := by exact_mod_cast hqdeg T hT
      _ < (k : WithBot ℕ) := by exact_mod_cast hk1
    · -- agreement ≥ rm via the index fibre
      have hsub : Finset.univ.filter (fun i : Fin n => (g ^ (i : ℕ)) ^ m ∈ T)
          ⊆ Finset.univ.filter (fun i : Fin n =>
            (qf T hT).eval (g ^ (i : ℕ))
              = (g ^ (i : ℕ)) ^ (r * m) + lam * (g ^ (i : ℕ)) ^ ((r - 1) * m)) := by
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (hqag T hT (g ^ (i : ℕ)) (Finset.mem_filter.mp hi).2).symm⟩
      have hcard := hfibcard T hTsub
      have hle := Finset.card_le_card hsub
      have himle : (Finset.univ.filter (fun i : Fin n => (g ^ (i : ℕ)) ^ m ∈ T)).card
          = m * T.card := by
        have hinj2 : Set.InjOn (fun i : Fin n => g ^ (i : ℕ))
            ↑(Finset.univ.filter (fun i : Fin n => (g ^ (i : ℕ)) ^ m ∈ T)) := by
          intro a _ b _ hab
          exact Fin.ext (pow_inj_llf (g_ne_zero_llf hn1 hg) hg
            a a.isLt b b.isLt hab)
        rw [← Finset.card_image_of_injOn hinj2]
        exact hcard
      rw [himle, hTcard, Nat.mul_comm] at hle
      exact hle
  · -- injectivity: equal interpolant functions force equal subsets
    intro T₁ hT₁ T₂ hT₂ heq
    by_contra hne
    have hT₁' := Finset.mem_coe.mp hT₁
    have hT₂' := Finset.mem_coe.mp hT₂
    rw [hf] at heq
    simp only [dif_pos hT₁', dif_pos hT₂'] at heq
    obtain ⟨hT₁mem, hT₁lam⟩ := Finset.mem_filter.mp hT₁'
    obtain ⟨hT₂mem, hT₂lam⟩ := Finset.mem_filter.mp hT₂'
    have hT₁sub : T₁ ⊆ G := (Finset.mem_powersetCard.mp hT₁mem).1
    have hT₂sub : T₂ ⊆ G := (Finset.mem_powersetCard.mp hT₂mem).1
    have hT₁card : T₁.card = r := (Finset.mem_powersetCard.mp hT₁mem).2
    have hT₂card : T₂.card = r := (Finset.mem_powersetCard.mp hT₂mem).2
    -- the difference polynomial
    set D : Polynomial (ZMod p) :=
      Polynomial.X ^ (r * m) + Polynomial.C lam * Polynomial.X ^ ((r - 1) * m)
        - qf T₁ hT₁' with hD
    -- D vanishes on the fibre union of T₁ ∪ T₂
    have hvan : ∀ x ∈ ((Finset.univ.filter (fun i : Fin n =>
        (g ^ (i : ℕ)) ^ m ∈ T₁ ∪ T₂)).image (fun i : Fin n => g ^ (i : ℕ))),
        D.eval x = 0 := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hmem := (Finset.mem_filter.mp hi).2
      rw [hD]
      simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      rcases Finset.mem_union.mp hmem with h1 | h2
      · rw [← hqag T₁ hT₁' (g ^ (i : ℕ)) h1]
        ring
      · have e2 := hqag T₂ hT₂' (g ^ (i : ℕ)) h2
        have efun : (qf T₁ hT₁').eval (g ^ (i : ℕ))
            = (qf T₂ hT₂').eval (g ^ (i : ℕ)) := congrFun heq i
        rw [efun, ← e2]
        ring
    -- the root set is too large
    have hUcard : (T₁ ∪ T₂).card ≥ r + 1 := by
      have h12 : T₁.card = T₂.card := by rw [hT₁card, hT₂card]
      by_contra hlt
      push Not at hlt
      have hsub12 : T₁ ⊆ T₁ ∪ T₂ := Finset.subset_union_left
      have hsub21 : T₂ ⊆ T₁ ∪ T₂ := Finset.subset_union_right
      have hc1 := Finset.card_le_card hsub12
      have heq1 : T₁ = T₁ ∪ T₂ := Finset.eq_of_subset_of_card_le hsub12 (by omega)
      have heq2 : T₂ = T₁ ∪ T₂ := Finset.eq_of_subset_of_card_le hsub21 (by omega)
      exact hne (heq1.trans heq2.symm)
    have hrootcard : ((Finset.univ.filter (fun i : Fin n =>
        (g ^ (i : ℕ)) ^ m ∈ T₁ ∪ T₂)).image (fun i : Fin n => g ^ (i : ℕ))).card
        = m * (T₁ ∪ T₂).card :=
      hfibcard (T₁ ∪ T₂) (Finset.union_subset hT₁sub hT₂sub)
    have hDdeg : D.degree ≤ ((r * m : ℕ) : WithBot ℕ) := by
      rw [hD]
      refine le_trans (Polynomial.degree_sub_le _ _) (max_le (le_trans
        (Polynomial.degree_add_le _ _) (max_le ?_ ?_)) ?_)
      · rw [Polynomial.degree_X_pow]
      · refine le_trans (Polynomial.degree_mul_le _ _) ?_
        calc (Polynomial.C lam).degree + (Polynomial.X ^ ((r - 1) * m) :
              Polynomial (ZMod p)).degree
            ≤ 0 + (((r - 1) * m : ℕ) : WithBot ℕ) := by
              refine add_le_add (Polynomial.degree_C_le) ?_
              rw [Polynomial.degree_X_pow]
        _ ≤ (((r * m) : ℕ) : WithBot ℕ) := by
              rw [zero_add]
              exact_mod_cast Nat.mul_le_mul_right m (by omega : r - 1 ≤ r)
      · calc (qf T₁ hT₁').degree ≤ ((qf T₁ hT₁').natDegree : WithBot ℕ) :=
              Polynomial.degree_le_natDegree
        _ ≤ (((r - 2) * m : ℕ) : WithBot ℕ) := by exact_mod_cast hqdeg T₁ hT₁'
        _ ≤ (((r * m) : ℕ) : WithBot ℕ) := by
              exact_mod_cast Nat.mul_le_mul_right m (by omega : r - 2 ≤ r)
    have hDzero : D = 0 := by
      refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
        (s := (Finset.univ.filter (fun i : Fin n =>
          (g ^ (i : ℕ)) ^ m ∈ T₁ ∪ T₂)).image (fun i : Fin n => g ^ (i : ℕ)))
        ?_ hvan
      rw [hrootcard]
      refine lt_of_le_of_lt hDdeg ?_
      have : r * m < m * (T₁ ∪ T₂).card := by
        calc r * m < (r + 1) * m := by
              exact (Nat.mul_lt_mul_right (show 0 < m by omega)).mpr (by omega)
        _ ≤ (T₁ ∪ T₂).card * m := Nat.mul_le_mul_right m hUcard
        _ = m * (T₁ ∪ T₂).card := Nat.mul_comm _ _
      exact_mod_cast this
    -- but the X^{rm} coefficient of D is 1
    have hcoeff := congrArg (fun q : Polynomial (ZMod p) => q.coeff (r * m)) hDzero
    simp only [hD, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_zero,
      Polynomial.coeff_X_pow, if_pos rfl] at hcoeff
    have hc1 : (Polynomial.C lam * Polynomial.X ^ ((r - 1) * m) :
        Polynomial (ZMod p)).coeff (r * m) = 0 := by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (by
          intro h
          have : (r - 1) * m < r * m :=
            (Nat.mul_lt_mul_right (show 0 < m by omega)).mpr (by omega)
          omega), mul_zero]
    have hc2 : (qf T₁ hT₁').coeff (r * m) = 0 := by
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      have h1 := hqdeg T₁ hT₁'
      have h2 : (r - 2) * m < r * m :=
        (Nat.mul_lt_mul_right (show 0 < m by omega)).mpr (by omega)
      omega
    rw [hc1, hc2] at hcoeff
    simp at hcoeff

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.ladder_list_ge_fibre
