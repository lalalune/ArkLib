/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/

import Mathlib.Tactic.FieldSimp

import ArkLib.Data.Fin.Sigma
import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.Stir.ProximityBound
import ArkLib.ProofSystem.Stir.ProximityGap

/-! Section 4.5 from STIR [ACFY24stir]

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing
    with fewer queries*][ACFY24stir]
-/

open BigOperators Finset NNReal Code

namespace Combine
variable {m : ℕ}
         {F : Type*} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type*} [Fintype ι]

/-- Fact 4.10
  Geometric series formula in a field, for a unit `r : F`. -/
lemma geometric_sum_units {F : Type*} [Field F] [DecidableEq F] {r : Fˣ} {a : ℕ} :
  ∑ j ∈ range (a + 1), (r ^ j : F) =
    if r = 1 then (a + 1 : F)
    else (1 - r ^ (a + 1)) / (1 - r) := by
  by_cases h : r = 1
  · rw [h]
    simp
  · simp only [h, ↓reduceIte]
    rw [geom_sum_eq]
    · have {a b : F} : a / b = -a / -b := by
        field_simp
      rw [@this _ (1 - ↑r)]
      simp
    · simp only [ne_eq, Units.val_eq_one]
      exact h

def ri (dstar : ℕ) (degs : Fin m → ℕ) (r : F) (i : Fin m) : F :=
          match i.1 with
          | 0 => 1
          | .succ i' =>
            let exp := i' + ∑ j < i, (dstar - degs j)
            r ^ exp

/-- Definition 4.11.1
    Combine(d*, r, (f_0, d_0), …, (f_{m-1}, d_{m-1}))(x)
      := sum_{i < m} r_i * f_i(x) * ( sum_{l < (d* - d_i + 1)} (r * φ(x))^l ) -/
def combine
  (φ : ι ↪ F) (dstar : ℕ) (r : F) (fs : Fin m → ι → F) (degs : Fin m → ℕ) (x : ι) : F :=
    ∑ i, (ri dstar degs r i) * (fs i x) * (∑ l ∈ range (dstar - degs i + 1), ((φ x) * r)^l)

/-- Definition 4.11.2
    Combine(d*, r, (f_0, d_0), …, (f_{m-1}, d_{m-1}))(x) :=
      if (r * φ(x)) = 1 then sum_{i < m} r_i * f_i(x) * (dstar - degree + 1)
      else sum_{i < m} r_i * f_i(x) * (1 - r * φ(x)^(dstar - degree + 1)) / (1 - r * φ(x))
-/
lemma combine_eq_cases {F ι : Type*} [Field F] [DecidableEq F]
  (φ : ι ↪ F) (dstar : ℕ) (r : F) (fs : Fin m → ι → F) (degs : Fin m → ℕ)
    (hdegs : ∀ i, degs i ≤ dstar) :
  combine φ dstar r fs degs =
    fun x =>
      let q := φ x * r
      if q ≠ 1
      then ∑ i, (ri dstar degs r i) * (fs i x) * (1 - q^(dstar - degs i + 1)) / (1 - q)
      else ∑ i, (ri dstar degs r i) * (fs i x) *  (dstar - degs i + 1) := by
  ext x
  unfold combine
  simp only
  by_cases h : r = 0
  · aesop
  · by_cases h' : φ x * r = 1
    · aesop
    · simp only [ne_eq, h', not_false_eq_true, ↓reduceIte]
      congr
      ext i
      have :
        ri dstar degs r i * fs i x * (1 - (φ x * r) ^ (dstar - degs i + 1)) / (1 - φ x * r) =
          (ri dstar degs r i * fs i x) * ((1 - (φ x * r) ^ (dstar - degs i + 1)) / (1 - φ x * r))
        := by
          field_simp
      rw [this]
      congr
      by_cases hq0 : φ x * r = 0
      · -- q = 0: the geometric series collapses to 1, and the closed form is also 1
        simp [hq0]
      · have := GroupWithZero.eq_zero_or_unit (φ x * r)
        rcases this with h0 | ⟨r', hr'⟩
        · exact (hq0 h0).elim
        · rw [hr', geometric_sum_units]
          have : r' ≠ 1 := by
            -- `q ≠ 1` in this branch and `q = r'`
            intro hEq
            apply h'
            simpa [hEq] using hr'
          simp [this]

-- def DegCor

/-- Definition 4.12.1
    DegCor(d*, r, f, degree)(x) := f(x) * ( sum_{ l < d* - d + 1 } (r * φ(x))^l ) -/
def degCor
  (φ : ι ↪ F) (dstar degree : ℕ) (r : F) (f : ι → F) (x : ι) : F :=
    f x * ∑ l ∈ range (dstar - degree + 1), ((φ x) * r) ^ l

/-- Definition 4.12.2
    DegCor(d*, r, f, d)(x) := f(x) * conditionalExp(x) -/
lemma degreeCor_eq {F : Type u_1} [Field F] [DecidableEq F] {ι : Type u_2} (φ : ι ↪ F)
  (dstar degree : ℕ) (r : F) (f : ι → F) (hd : degree ≤ dstar) (x : ι) :
  let q := φ x * r
  degCor φ dstar degree r f x =
    if q ≠ 1
    then f x * (1 - q^(dstar - degree + 1)) / (1 - q)
    else f x * (dstar - degree + 1) := by
  intros q
  unfold degCor
  by_cases h : q = 1
  · simp only [h, ne_eq, not_true_eq_false, ↓reduceIte]
    congr
    rcases GroupWithZero.eq_zero_or_unit (φ x * r) with h' | h'
    · aesop
    · dsimp [q] at h
      rcases h' with ⟨r', h'⟩
      rw [h', geometric_sum_units]
      aesop
  · simp only [ne_eq, h, not_false_eq_true, ↓reduceIte]
    have :
      f x * (1 - q ^ (dstar - degree + 1)) / (1 - q) =
        f x * ((1 - q ^ (dstar - degree + 1)) / (1 - q)) := by
      field_simp
    rw [this]
    congr
    rcases GroupWithZero.eq_zero_or_unit (φ x * r) with h' | h'
    · aesop
    · rcases h' with ⟨r', h'⟩
      rw [h', geometric_sum_units]
      aesop


variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [Nonempty ι]

open LinearCode Classical ProbabilityTheory ReedSolomon STIR in
/-- Lemma 4.13
  Let `dstar` be the target degree, `f₁,...,f_{m-1} : ι → F`,
  `0 < degs₁,...,degs_{m-1} < dstar` be degrees and
  `δ ∈ (0, min{(1-BStar(ρ)), (1-ρ-1/|ι|)})` be a distance parameter, then
      Pr_{r ← F} [δᵣ(Combine(dstar,r,(f₁,degs₁),...,(fₘ,degsₘ)))]
                   > err' (dstar, ρ, δ, m * (dstar + 1) - ∑ i degsᵢ) -/
lemma combine_theorem
  {φ : ι ↪ F} {dstar m : ℕ}
  (fs : Fin m → ι → F) (degs : Fin m → ℕ) (hdegs : ∀ i, degs i ≤ dstar)
  (δ : ℝ≥0) (hδPos : δ > 0)
  (hδLt : δ < (min (1 - Bstar (rate (code φ dstar)))
                   (1 - (rate (code φ dstar)) - 1 / Fintype.card ι)))
  (hProb : Pr_{ let r ← $ᵖ F}[δᵣ((combine φ dstar r fs degs), (code φ dstar)) ≤ δ] >
    proximityError F dstar (rate (code φ dstar)) δ (m * (dstar + 1) - ∑ i, degs i)) :
    jointAgreement (F := F) (κ := Fin m) (ι := ι) (C := code φ dstar)
      (W := fs) (δ := δ)
    := by
  classical
  let nterms : Fin m → ℕ := fun i => dstar - degs i + 1
  let K := (i : Fin m) × Fin (nterms i)
  let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let fexp : Fin (Fintype.card K) → ι → F :=
    fun k x => fs (e k).1 x * (φ x) ^ ((e k).2 : ℕ)
  let gen : F → Fin (Fintype.card K) → F :=
    fun r k => ri dstar degs r (e k).1 * r ^ ((e k).2 : ℕ)
  have hδLt' : δ < 1 - Bstar (rate (code φ dstar)) := by
    exact lt_of_lt_of_le hδLt (min_le_left _ _)
  have hcardK :
      Fintype.card K = m * (dstar + 1) - ∑ i : Fin m, degs i := by
    have hsum :
        (∑ i : Fin m, nterms i) = m * (dstar + 1) - ∑ i : Fin m, degs i := by
      calc
        (∑ i : Fin m, nterms i) = ∑ i : Fin m, ((dstar + 1) - degs i) := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [nterms]
          have hi := hdegs i
          omega
        _ = (∑ _ : Fin m, (dstar + 1)) - ∑ i : Fin m, degs i := by
          simpa using Finset.sum_tsub_distrib (s := Finset.univ)
            (f := fun _ : Fin m => dstar + 1) (g := degs) (by
              intro i _
              exact Nat.le_trans (hdegs i) (Nat.le_succ dstar))
        _ = m * (dstar + 1) - ∑ i : Fin m, degs i := by
          simp [Finset.sum_const]
    calc
      Fintype.card K = ∑ i : Fin m, nterms i := by
        simp [K]
      _ = m * (dstar + 1) - ∑ i : Fin m, degs i := hsum
  have hcombine :
      (fun r : F => (fun x : ι => ∑ j : Fin (Fintype.card K), gen r j * fexp j x)) =
        (fun r : F => combine φ dstar r fs degs) := by
    funext r x
    simp only [combine, gen, fexp]
    rw [(Equiv.sum_comp e (fun k : K =>
      ri dstar degs r k.1 * r ^ (k.2 : ℕ) * (fs k.1 x * φ x ^ (k.2 : ℕ))))]
    change (∑ k : K, ri dstar degs r k.1 * r ^ (k.2 : ℕ) *
        (fs k.1 x * φ x ^ (k.2 : ℕ))) =
      ∑ i, ri dstar degs r i * fs i x *
        ∑ l ∈ range (dstar - degs i + 1), (φ x * r) ^ l
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_fin_eq_sum_range]
    simp only [nterms]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    rw [dif_pos (by
      have hl' := Finset.mem_range.mp hl
      omega)]
    ring_nf
  have hProb' :
      Pr_{ let r ← $ᵖ F}[
        δᵣ((fun x => ∑ j : Fin (Fintype.card K), gen r j * fexp j x), code φ dstar) ≤ δ] >
      ENNReal.ofReal
        (proximityError F dstar (rate (code φ dstar)) δ (Fintype.card K)) := by
    have hProb₁ :
        Pr_{ let r ← $ᵖ F}[δᵣ((combine φ dstar r fs degs), code φ dstar) ≤ δ] >
        ENNReal.ofReal
          (proximityError F dstar (rate (code φ dstar)) δ (Fintype.card K)) := by
      rw [hcardK]
      simpa using hProb
    have hcombine_app :
        ∀ r : F, (fun x : ι => ∑ j : Fin (Fintype.card K), gen r j * fexp j x) =
          combine φ dstar r fs degs := by
      intro r
      exact congrFun hcombine r
    simpa [hcombine_app] using hProb₁
  rcases STIR.proximity_gap (φ := φ) (degree := dstar) (m := Fintype.card K)
      (δ := δ) (f := fexp) (GenFun := gen) hδPos hδLt' hProb' with
    ⟨S, hS, hclose⟩
  refine ⟨S, hS, ?_⟩
  choose v hv_mem hv_agree using
    (fun i : Fin m => hclose (e.symm ⟨i, ⟨0, by simp [nterms]⟩⟩))
  refine ⟨v, fun i => ?_⟩
  constructor
  · exact hv_mem i
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    let pair : K := ⟨i, ⟨0, by simp [nterms]⟩⟩
    have h : fexp (e.symm pair) x = v i x := by
      simpa [pair] using hv_agree i x hx
    have hfs : fexp (e.symm pair) x = fs i x := by
      have heq : e (e.symm pair) = pair := Equiv.apply_symm_apply e pair
      change fs (e (e.symm pair)).1 x * φ x ^ ((e (e.symm pair)).2 : ℕ) = fs i x
      rw [heq]
      simp [pair]
    exact h.symm.trans hfs

end Combine
