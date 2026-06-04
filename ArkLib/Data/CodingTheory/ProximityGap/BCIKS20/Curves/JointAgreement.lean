/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Prelude
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.GoodCoeffs
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Joint agreement for parameterized curves ([BCIKS20] §6.1)

Curves analogue of `AffineLines/JointAgreement.lean`: the bivariate
Berlekamp–Welch construction over the degree-`k` curve words. The kernel
coefficients have `Y`-degrees `k·e` / `k·(e+1)` (the line case is `k = 1`).
-/

namespace ProximityGap

-- Decidability/Fintype instances are threaded through the section; several
-- statement-level lemmas do not mention them directly.
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

open scoped BigOperators in
open scoped Polynomial.Bivariate in
open Polynomial in
open Polynomial.Bivariate in
open BerlekampWelch in
omit [DecidableEq ι] in
theorem RS_exists_bivariate_AB_of_goodCoeffsCurve_card_gt
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg))
    (u : WordStack F (Fin (k + 1)) ι)
    (hS : (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k *
      Fintype.card ι) :
    ∃ A B : F[X][Y],
      A ≠ 0 ∧
      Polynomial.Bivariate.degreeX A ≤ Nat.floor (δ * Fintype.card ι) ∧
      Polynomial.Bivariate.natDegreeY A ≤ k * Nat.floor (δ * Fintype.card ι) ∧
      Polynomial.Bivariate.degreeX B ≤ Nat.floor (δ * Fintype.card ι) + deg - 1 ∧
      Polynomial.Bivariate.natDegreeY B ≤ k * (Nat.floor (δ * Fintype.card ι) + 1) ∧
      (∀ i : ι,
        Polynomial.Bivariate.evalX (domain i) B =
          (∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)) *
            Polynomial.Bivariate.evalX (domain i) A) := by
  classical
  let e : ℕ := Nat.floor (δ * Fintype.card ι)
  have hker :
      ∃ a : Fin (e + 1) → F[X],
        ∃ b : Fin (e + deg) → F[X],
          a ≠ 0 ∧
            (∀ t, (a t).natDegree ≤ k * e) ∧
              (∀ s, (b s).natDegree ≤ k * (e + 1)) ∧
                Matrix.mulVec
                    (BW_homMatrix (ι := ι) e deg
                      (fun i => (Polynomial.C (domain i) : F[X]))
                      (fun i => ∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)))
                    (Fin.append a b) = 0 := by
    simpa [e] using
      (RS_exists_kernelVec_BW_homMatrix_of_goodCoeffsCurve_card_gt (k := k) (deg := deg) (domain
        := domain)
        (δ := δ) u hdeg hδ hS)
  rcases hker with ⟨a, b, ha_ne, ha_deg, hb_deg, hMul⟩
  let A0 : F[X][Y] := ∑ t : Fin (e + 1), Polynomial.monomial t.1 (a t)
  let B0 : F[X][Y] := ∑ s : Fin (e + deg), Polynomial.monomial s.1 (b s)
  let A : F[X][Y] := (Polynomial.Bivariate.swap (R := F)) A0
  let B : F[X][Y] := (Polynomial.Bivariate.swap (R := F)) B0
  have hcoeffA0 : ∀ n : ℕ, ∀ hn : n < e + 1, A0.coeff n = a ⟨n, hn⟩ := by
    intro n hn
    classical
    simp [A0, Polynomial.coeff_monomial]
    have hsum :
        (∑ t : Fin (e + 1), (if t = ⟨n, hn⟩ then a t else (0 : F[X]))) = a ⟨n, hn⟩ := by
      simp
    simpa [Fin.ext_iff] using hsum
  have hcoeffB0 : ∀ n : ℕ, ∀ hn : n < e + deg, B0.coeff n = b ⟨n, hn⟩ := by
    intro n hn
    classical
    simp [B0, Polynomial.coeff_monomial]
    have hsum :
        (∑ t : Fin (e + deg), (if t = ⟨n, hn⟩ then b t else (0 : F[X]))) = b ⟨n, hn⟩ := by
      simp
    simpa [Fin.ext_iff] using hsum
  have hcoeffA0_big : ∀ N : ℕ, e < N → A0.coeff N = 0 := by
    intro N hN
    classical
    have hN' : e + 1 ≤ N := Nat.succ_le_of_lt hN
    have hne : ∀ t : Fin (e + 1), (t : ℕ) ≠ N := by
      intro t
      have ht : (t : ℕ) < N := lt_of_lt_of_le t.2 hN'
      exact Nat.ne_of_lt ht
    simp [A0, Polynomial.coeff_monomial, hne]
  have hcoeffB0_big : ∀ N : ℕ, e + deg - 1 < N → B0.coeff N = 0 := by
    intro N hN
    classical
    have hdegpos : 0 < deg := Nat.pos_of_ne_zero (NeZero.ne deg)
    have hpos : 1 ≤ e + deg := Nat.succ_le_of_lt (Nat.add_pos_right e hdegpos)
    have hN' : e + deg ≤ N := by
      have : (e + deg - 1) + 1 ≤ N := by
        simpa [Nat.succ_eq_add_one] using Nat.succ_le_of_lt hN
      simpa [Nat.sub_add_cancel hpos, Nat.add_assoc] using this
    have hne : ∀ t : Fin (e + deg), (t : ℕ) ≠ N := by
      intro t
      have ht : (t : ℕ) < N := lt_of_lt_of_le t.2 hN'
      exact Nat.ne_of_lt ht
    simp [B0, Polynomial.coeff_monomial, hne]
  refine ⟨A, B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- A ≠ 0
    have hex : ∃ t : Fin (e + 1), a t ≠ 0 := by
      by_contra h
      apply ha_ne
      funext t
      have : a t = 0 := by
        by_contra ht
        exact h ⟨t, ht⟩
      simpa using this
    rcases hex with ⟨t0, ht0⟩
    have hcoeff : A0.coeff t0.1 = a t0 := by
      simpa using (hcoeffA0 t0.1 t0.2)
    have hA0 : A0 ≠ 0 := by
      intro hzero
      apply ht0
      have : A0.coeff t0.1 = 0 := by simp [hzero]
      simpa [hcoeff] using this
    intro hzero
    apply hA0
    exact (Polynomial.Bivariate.swap (R := F)).injective (by simp [A, hzero])
  · -- degreeX A bound
    have hnatY_A0 : Polynomial.Bivariate.natDegreeY A0 ≤ e := by
      unfold Polynomial.Bivariate.natDegreeY
      exact (Polynomial.natDegree_le_iff_coeff_eq_zero).2 hcoeffA0_big
    have hdegX : Polynomial.Bivariate.degreeX A = Polynomial.Bivariate.natDegreeY A0 := by
      simpa [A] using (ps_degree_x_swap (F := F) (f := A0))
    simpa [hdegX] using hnatY_A0
  · -- natDegreeY A bound
    have hdegX_A0 : Polynomial.Bivariate.degreeX A0 ≤ k * e := by
      classical
      unfold Polynomial.Bivariate.degreeX
      refine Finset.sup_le_iff.2 ?_
      intro n hn
      by_cases hnlt : n < e + 1
      · have : (A0.coeff n).natDegree = (a ⟨n, hnlt⟩).natDegree := by
          simp [hcoeffA0 n hnlt]
        simpa [this] using ha_deg ⟨n, hnlt⟩
      · have hnle : e < n := by
          have : e + 1 ≤ n := Nat.le_of_not_gt hnlt
          exact lt_of_lt_of_le (Nat.lt_succ_self e) this
        have hcoeff0 : A0.coeff n = 0 := hcoeffA0_big n hnle
        have : A0.coeff n ≠ 0 := by
          simpa [Polynomial.mem_support_iff] using hn
        exact (this hcoeff0).elim
    have hnatY : Polynomial.Bivariate.natDegreeY A = Polynomial.Bivariate.degreeX A0 := by
      simpa [A] using (ps_nat_degree_y_swap (F := F) (f := A0))
    simpa [hnatY] using hdegX_A0
  · -- degreeX B bound
    have hnatY_B0 : Polynomial.Bivariate.natDegreeY B0 ≤ e + deg - 1 := by
      unfold Polynomial.Bivariate.natDegreeY
      exact (Polynomial.natDegree_le_iff_coeff_eq_zero).2 hcoeffB0_big
    have hdegX : Polynomial.Bivariate.degreeX B = Polynomial.Bivariate.natDegreeY B0 := by
      simpa [B] using (ps_degree_x_swap (F := F) (f := B0))
    simpa [hdegX] using hnatY_B0
  · -- natDegreeY B bound
    have hdegX_B0 : Polynomial.Bivariate.degreeX B0 ≤ k * (e + 1) := by
      classical
      unfold Polynomial.Bivariate.degreeX
      refine Finset.sup_le_iff.2 ?_
      intro n hn
      by_cases hnlt : n < e + deg
      · have : (B0.coeff n).natDegree = (b ⟨n, hnlt⟩).natDegree := by
          simp [hcoeffB0 n hnlt]
        simpa [this] using hb_deg ⟨n, hnlt⟩
      · have hdegpos : 0 < deg := Nat.pos_of_ne_zero (NeZero.ne deg)
        have hpos : 0 < e + deg := Nat.add_pos_right e hdegpos
        have hnge : e + deg ≤ n := (Nat.not_lt).1 hnlt
        have hnle : e + deg - 1 < n := Nat.sub_one_lt_of_le hpos hnge
        have hcoeff0 : B0.coeff n = 0 := hcoeffB0_big n hnle
        have : B0.coeff n ≠ 0 := by
          simpa [Polynomial.mem_support_iff] using hn
        exact (this hcoeff0).elim
    have hnatY : Polynomial.Bivariate.natDegreeY B = Polynomial.Bivariate.degreeX B0 := by
      simpa [B] using (ps_nat_degree_y_swap (F := F) (f := B0))
    simpa [hnatY] using hdegX_B0
  · -- main identity
    intro i
    have hEvalX_A :
        Polynomial.Bivariate.evalX (domain i) A =
          Polynomial.Bivariate.evalY (domain i) A0 := by
      simpa [A] using (ps_eval_y_eq_eval_x_swap (F := F) (y := domain i) (f := A0)).symm
    have hEvalX_B :
        Polynomial.Bivariate.evalX (domain i) B =
          Polynomial.Bivariate.evalY (domain i) B0 := by
      simpa [B] using (ps_eval_y_eq_eval_x_swap (F := F) (y := domain i) (f := B0)).symm
    rw [hEvalX_B, hEvalX_A]
    have hEq_all :
        ∀ i : ι,
          (∑ t : Fin (e + 1), a t * (Polynomial.C (domain i) : F[X]) ^ t.1) *
              (∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ))
            = ∑ s : Fin (e + deg), b s * (Polynomial.C (domain i) : F[X]) ^ s.1 :=
      (BW_homMatrix_mulVec_eq_zero_iff (ι := ι) (R := F[X]) e deg
          (fun i => (Polynomial.C (domain i) : F[X]))
          (fun i => ∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ))
          a b).1 hMul
    have hEvalA :
        Polynomial.Bivariate.evalY (domain i) A0 =
          ∑ t : Fin (e + 1), a t * (Polynomial.C (domain i) : F[X]) ^ t.1 := by
      classical
      simp [Polynomial.Bivariate.evalY, A0, Polynomial.eval_finset_sum]
    have hEvalB :
        Polynomial.Bivariate.evalY (domain i) B0 =
          ∑ s : Fin (e + deg), b s * (Polynomial.C (domain i) : F[X]) ^ s.1 := by
      classical
      simp [Polynomial.Bivariate.evalY, B0, Polynomial.eval_finset_sum]
    have hEq_eval :
        Polynomial.Bivariate.evalY (domain i) A0 *
            (∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ))
          = Polynomial.Bivariate.evalY (domain i) B0 := by
      simpa [hEvalA, hEvalB] using (hEq_all i)
    calc
      Polynomial.Bivariate.evalY (domain i) B0
          = Polynomial.Bivariate.evalY (domain i) A0 *
              (∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)) := by
              simpa using hEq_eval.symm
      _ = (∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)) *
            Polynomial.Bivariate.evalY (domain i) A0 := by
            -- commutativity in `F[X]`
            exact (mul_comm (Polynomial.Bivariate.evalY (domain i) A0)
              (∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)))

end CoreResults

end ProximityGap
