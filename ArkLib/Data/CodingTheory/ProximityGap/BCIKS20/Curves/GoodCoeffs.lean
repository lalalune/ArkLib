/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Prelude
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.BWMatrix
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Good coefficients for parameterized curves ([BCIKS20] §6.1)

Curves analogue of `AffineLines/GoodCoeffs.lean`: the set of curve parameters
`z` at which the degree-`k` parameterized curve through the words
`u 0, …, u k` is `δ`-close to the Reed–Solomon code, and the per-parameter
close-codeword extraction. The line case is `k = 1`
(`u 0 + z • u 1 = ∑ t : Fin 2, z ^ t • u t`).
-/

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The set of curve parameters `z : F` at which the degree-`k` parameterized
curve through `u 0, …, u k` is `δ`-close to the Reed–Solomon code. Curves
analogue of `RS_goodCoeffs` (the line case is `k = 1`). -/
noncomputable def RS_goodCoeffsCurve {k deg : ℕ} {domain : ι ↪ F}
    (u : WordStack F (Fin (k + 1)) ι) (δ : ℝ≥0) : Finset F :=
  Finset.filter
    (fun z : F =>
      δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, ReedSolomon.code domain deg) ≤ δ)
    Finset.univ

open Polynomial in
/-- At every good curve parameter there is a codeword polynomial within the
floor-`δ` Hamming radius. Curves analogue of `RS_exists_Pz_of_mem_goodCoeffs`. -/
theorem RS_exists_Pz_of_mem_goodCoeffsCurve {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg] (u : WordStack F (Fin (k + 1)) ι) {z : F}
    (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) :
    ∃ Pz : F[X], Pz.natDegree < deg ∧
      Δ₀(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, Pz.eval ∘ domain)
        ≤ Nat.floor (δ * Fintype.card ι) := by
  classical
  have hrel :
      δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, ReedSolomon.code domain deg) ≤ δ := by
    simpa [RS_goodCoeffsCurve] using hz
  let e : ℕ := Nat.floor (δ * Fintype.card ι)
  have hdist :
      Δ₀(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
        (ReedSolomon.code domain deg : Set (ι → F))) ≤ (e : ℕ∞) := by
    have h :=
      (Code.relDistFromCode_le_iff_distFromCode_le
          (u := ∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t)
          (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)).1 hrel
    simpa [e] using h
  rcases
      (Code.closeToCode_iff_closeToCodeword_of_minDist
            (u := ∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t)
            (C := (ReedSolomon.code domain deg : Set (ι → F))) (e := e)).1 hdist with
    ⟨v, hvC, hvdist⟩
  rcases hvC with ⟨Pz, hPz, rfl⟩
  refine ⟨Pz, ?_, ?_⟩
  · exact ReedSolomon.natDegree_lt_of_mem_degreeLT (deg := deg) hPz
  · simpa [e] using hvdist

open scoped BigOperators in
open Polynomial in
theorem RS_exists_kernelVec_BW_homMatrix_eval_of_mem_goodCoeffsCurve
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin (k + 1)) ι) {z : F}
    (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) :
    let e : ℕ := Nat.floor (δ * Fintype.card ι)
    ∃ a : Fin (e + 1) → F,
      ∃ b : Fin (e + deg) → F,
        a ≠ 0 ∧
          Matrix.mulVec
              (BW_homMatrix (ι := ι) e deg (fun i => domain i)
                (fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i))
              (Fin.append a b) = 0 := by
  classical
  -- Unfold the `let e := ...` in the goal, but avoid changing the quantifier structure
  simp only
  -- Name the error bound (this rewrites occurrences of the floor expression)
  set e : ℕ := Nat.floor (δ * Fintype.card ι) with he
  -- Get the close polynomial `Pz`
  obtain ⟨Pz, hPzdeg, hdist⟩ :=
    RS_exists_Pz_of_mem_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) (δ := δ) u (z := z) hz
  have hdist' : Δ₀(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, Pz.eval ∘ domain) ≤ e := by
    simpa [he] using hdist
  -- Extract a small set of disagreement coordinates
  obtain ⟨D, hDcard, hAgree⟩ :=
    (Code.closeToWord_iff_exists_possibleDisagreeCols
        (u := ∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t)
        (v := Pz.eval ∘ domain)
        (e := e)).1 hdist'
  -- Error-locator polynomial and the corresponding `Q`
  set E : F[X] := ∏ i ∈ D, (Polynomial.X - Polynomial.C (domain i)) with hE
  set Q : F[X] := E * Pz with hQ
  -- Coefficient vectors (truncated to the required degrees)
  let a : Fin (e + 1) → F := fun t => E.coeff t.1
  let b : Fin (e + deg) → F := fun s => Q.coeff s.1
  have hE_monic : E.Monic := by
    -- `E` is a product of monic linear factors
    simpa [hE] using (Polynomial.monic_prod_X_sub_C (b := fun i : ι => domain i) (s := D))
  have hE_natDegree : E.natDegree = D.card := by
    -- degree of product of monic polynomials is sum of degrees
    have hdeg :=
      Polynomial.natDegree_prod_of_monic (s := D)
        (f := fun i : ι => (Polynomial.X - Polynomial.C (domain i) : F[X]))
        (by
          intro i hi
          simpa using (Polynomial.monic_X_sub_C (domain i)))
    -- simplify the RHS
    convert hdeg using 1
    simp
  have hE_deg_lt : E.natDegree < e + 1 := by
    have : D.card < e + 1 := Nat.lt_succ_of_le hDcard
    simpa [hE_natDegree] using this
  have hQ_deg_lt : Q.natDegree < e + deg := by
    -- `natDegree (E*Pz) ≤ natDegree E + natDegree Pz`
    have hmul : Q.natDegree ≤ E.natDegree + Pz.natDegree := by
      simpa [hQ] using (Polynomial.natDegree_mul_le (p := E) (q := Pz))
    have hPz_le : Pz.natDegree ≤ deg - 1 := Nat.le_pred_of_lt hPzdeg
    have hE_le : E.natDegree ≤ e := by
      simpa [hE_natDegree] using hDcard
    have hsum_le : E.natDegree + Pz.natDegree ≤ e + (deg - 1) := Nat.add_le_add hE_le hPz_le
    have hle : Q.natDegree ≤ e + (deg - 1) := le_trans hmul (by simpa [Nat.add_assoc] using hsum_le)
    -- turn into a strict inequality
    have hdegpos : 0 < deg := Nat.pos_of_neZero deg
    have : e + (deg - 1) < e + deg :=
      Nat.add_lt_add_left (Nat.pred_lt (Nat.ne_of_gt hdegpos)) e
    exact lt_of_le_of_lt hle this
  -- `a` is nonzero because the leading coefficient of `E` is 1
  have ha_ne : a ≠ 0 := by
    have hcard_lt : D.card < e + 1 := Nat.lt_succ_of_le hDcard
    let t0 : Fin (e + 1) := ⟨D.card, hcard_lt⟩
    have hcoeff : E.coeff D.card = 1 := by
      have hlead : E.leadingCoeff = 1 := hE_monic.leadingCoeff
      simpa [Polynomial.leadingCoeff, hE_natDegree] using hlead
    have ht0 : a t0 = 1 := by
      simpa [a, t0] using hcoeff
    intro hzero
    have hz0 : a t0 = 0 := by
      simpa using congrArg (fun f => f t0) hzero
    have h1 : (1 : F) = 0 := by
      rwa [ht0] at hz0
    exact one_ne_zero h1
  refine ⟨a, b, ha_ne, ?_⟩
  -- Show the vector is in the kernel via the characterization lemma
  apply (BW_homMatrix_mulVec_eq_zero_iff (ι := ι) (e := e) (k := deg)
      (ωs := fun i => domain i)
      (f := fun i => (∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i))
      (a := a) (b := b)).2
  intro i
  -- Convert the coefficient sums into polynomial evaluations
  have hsum_a : (∑ t : Fin (e + 1), a t * (domain i) ^ t.1) = E.eval (domain i) := by
    have hfin : (∑ t : Fin (e + 1), a t * (domain i) ^ t.1)
        = ∑ n ∈ Finset.range (e + 1), E.coeff n * (domain i) ^ n := by
      simpa [a] using
        (Fin.sum_univ_eq_sum_range (f := fun n : ℕ => E.coeff n * (domain i) ^ n) (n := e + 1))
    have heval : E.eval (domain i) = ∑ n ∈ Finset.range (e + 1), E.coeff n * (domain i) ^ n :=
      Polynomial.eval_eq_sum_range' (p := E) (n := e + 1) hE_deg_lt (domain i)
    simpa [hfin] using heval.symm
  have hsum_b : (∑ s : Fin (e + deg), b s * (domain i) ^ s.1) = Q.eval (domain i) := by
    have hfin : (∑ s : Fin (e + deg), b s * (domain i) ^ s.1)
        = ∑ n ∈ Finset.range (e + deg), Q.coeff n * (domain i) ^ n := by
      simpa [b] using
        (Fin.sum_univ_eq_sum_range (f := fun n : ℕ => Q.coeff n * (domain i) ^ n) (n := e + deg))
    have heval : Q.eval (domain i) = ∑ n ∈ Finset.range (e + deg), Q.coeff n * (domain i) ^ n :=
      Polynomial.eval_eq_sum_range' (p := Q) (n := e + deg) hQ_deg_lt (domain i)
    simpa [hfin] using heval.symm
  -- Reduce to showing `E.eval ω * f = Q.eval ω` and discharge by cases
  by_cases hiD : i ∈ D
  · -- On error positions, `E(ω_i)=0`
    have hE0 : E.eval (domain i) = 0 := by
      -- expand `E` and use that evaluation commutes with products
      rw [hE]
      rw [Polynomial.eval_prod (s := D)
        (p := fun j : ι => (Polynomial.X - Polynomial.C (domain j) : F[X]))
        (x := domain i)]
      refine Finset.prod_eq_zero hiD ?_
      simp
    calc
      (∑ t : Fin (e + 1), a t * (domain i) ^ t.1) * ((∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i))
          = (E.eval (domain i)) * ((∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i)) := by rw [hsum_a]
      _ = 0 := by simp [hE0]
      _ = Q.eval (domain i) := by
            have hmul_eval : Q.eval (domain i) = (E.eval (domain i)) * (Pz.eval (domain i)) := by
              rw [hQ, Polynomial.eval_mul]
            simp [hmul_eval, hE0]
      _ = ∑ s : Fin (e + deg), b s * (domain i) ^ s.1 := by rw [hsum_b]
  · -- On agreement positions, `f_i = Pz(ω_i)`
    have hf_eq : ((∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i)) = Pz.eval (domain i) := by
      have := hAgree i hiD
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    calc
      (∑ t : Fin (e + 1), a t * (domain i) ^ t.1) * ((∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i))
          = (E.eval (domain i)) * ((∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i)) := by rw [hsum_a]
      _ = (E.eval (domain i)) * (Pz.eval (domain i)) := by simp [hf_eq]
      _ = Q.eval (domain i) := by
            rw [hQ, Polynomial.eval_mul]
      _ = ∑ s : Fin (e + deg), b s * (domain i) ^ s.1 := by rw [hsum_b]

end CoreResults

end ProximityGap
