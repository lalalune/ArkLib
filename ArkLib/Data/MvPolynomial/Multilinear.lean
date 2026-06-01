/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.CharP.Basic

import CompPoly.Data.MvPolynomial.Notation
import ArkLib.Data.MvPolynomial.Interpolation

/-!
  # Multilinear Polynomials

  This is the special case of polynomial interpolation, when we consider multilinear polynomials and
  evaluation on the hypercube `σ → Fin 2`.
-/

noncomputable section

namespace MvPolynomial

open BigOperators Fintype Finset

universe u

variable {σ : Type*} {R : Type*}

instance coeFunctionFin2 [NatCast R] : Coe (σ → Fin 2) (σ → R) where
  coe := fun vec i => vec i

variable [CommRing R]

def toEvalsZeroOne (p : MvPolynomial σ R) : (σ → Fin 2) → R :=
  fun x => eval (x : σ → R) p

abbrev singleEqPolynomial (r : R) (x : MvPolynomial σ R) : MvPolynomial σ R :=
  (1 - C r) * (1 - x) + C r * x

theorem singleEqPolynomial_nf (r : R) (x : MvPolynomial σ R) :
    singleEqPolynomial r x = (2 * C r - 1) * x + (1 - C r) := by
  ring_nf

theorem singleEqPolynomial_symm (r : R) (s : R) :
    (singleEqPolynomial r (C s) : MvPolynomial σ R) = singleEqPolynomial s (C r) := by ring_nf

@[simp]
theorem singleEqPolynomial_zero (x : MvPolynomial σ R) : singleEqPolynomial (0 : R) x = 1 - x := by
  unfold singleEqPolynomial; simp

@[simp]
theorem singleEqPolynomial_one (x : MvPolynomial σ R) : singleEqPolynomial (1 : R) x = x := by
  unfold singleEqPolynomial; simp

-- @[simp]
theorem singleEqPolynomial_zeroOne (r : Fin 2) (x : MvPolynomial σ R) :
    singleEqPolynomial (r : R) x = if r = 0 then 1 - x else x := by
  fin_cases r <;> simp

-- @[simp]
theorem singleEqPolynomial_zeroOne_C (r : Fin 2) (x : Fin 2) :
    (singleEqPolynomial (r : R) (C x) : MvPolynomial σ R) = if x = r then 1 else 0 := by
  fin_cases r <;> fin_cases x <;> simp

-- @[simp]
-- theorem singleEqPolynomial_eval_zeroOne (x : Fin n → Fin 2) (r : Fin n → Fin 2) (i : Fin n) :
--     (eval fun i => ↑↑(x i))
--     (match r i with
--     | 0 => 1 - X i
--     | 1 => X i) = 1 := by

variable [Fintype σ]

abbrev eqPolynomial' : R[X (σ ⊕ σ)] :=
  ∏ i : σ, ((1 - X (.inl i)) * (1 - X (.inr i)) + (X (.inl i)) * X (.inr i))

-- Should be in `R[X σ ⊕ σ]`
abbrev eqPolynomial (r : σ → R) : R[X σ] :=
  ∏ i : σ, singleEqPolynomial (r i) (X i)

theorem eqPolynomial_expanded (r : σ → R) :
    eqPolynomial r = ∏ i : σ, ((1 - C (r i)) * (1 - X i) + C (r i) * X i) := rfl

theorem eqPolynomial_symm (x : σ → R) (y : σ → R) :
    MvPolynomial.eval y (eqPolynomial x) = MvPolynomial.eval x (eqPolynomial y) := by
  simp only [map_prod, map_add, map_mul, map_sub, map_one, eval_C, eval_X]
  congr
  funext
  ring_nf

-- @[simp]
theorem eqPolynomial_zeroOne (r : σ → Fin 2) : (eqPolynomial r : MvPolynomial σ R) =
    ∏ i : σ, if r i = 0 then 1 - X i else X i := by
  unfold eqPolynomial; congr; funext i; simp [singleEqPolynomial_zeroOne]

@[simp]
theorem eqPolynomial_eval_zeroOne (r x : σ → Fin 2) :
    eval (x : σ → R) (eqPolynomial r) = if x = r then 1 else 0 := by
  unfold eqPolynomial
  simp only [map_prod, map_add, map_natCast, map_mul, map_sub, map_one, eval_X]
  by_cases h : x = r
  · subst h
    have (i : Fin 2) : (1 - (i : R)) * (1 - (i : R)) + i * i = 1 := by
      fin_cases i <;> ring_nf <;> simp
    simp [this]
  · rw [if_neg h]
    have : ∃ i : σ, x i ≠ r i := Function.ne_iff.mp h
    obtain ⟨i, hi⟩ := this
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    by_cases h' : r i = 0
    · simp_all [Fin.eq_one_of_ne_zero]
    · have : x i = 0 := by fin_omega
      simp_all [Fin.eq_one_of_ne_zero]

variable [DecidableEq σ]

/-- Multilinear extension of evaluations on the `σ`-indexed hypercube, where the evaluations are
  represented as `(σ → Fin 2) → R` -/
def MLE (evals : (σ → Fin 2) → R) : MvPolynomial σ R :=
    ∑ x : σ → Fin 2, (eqPolynomial (x : σ → R)) * C (evals x)

/-- Multilinear extension of evaluations on the `n`-dimensional hypercube, where the evaluations are
  represented as `Fin (2 ^ n) → R` -/
def MLE' {n : ℕ} (evals : Fin (2 ^ n) → R) : MvPolynomial (Fin n) R :=
  MLE (evals ∘ finFunctionFinEquiv)

theorem MLE_expanded (evals : (σ → Fin 2) → R) : MLE evals =
    ∑ x : σ → Fin 2, (∏ i : σ, ((1 - C (x i : R)) * (1 - X i) + C (x i : R) * X i))
      * C (evals x) := by
  unfold MLE; congr

@[simp]
theorem MLE_eval_zeroOne (x : σ → Fin 2) (evals : (σ → Fin 2) → R) :
    MvPolynomial.eval (x : σ → R) (MLE evals) = evals x := by
  simp only [MLE, eval_sum, eval_mul, eqPolynomial_eval_zeroOne]
  simp

theorem eval_zeroOne_eq_MLE_toEvalsZeroOne (p : MvPolynomial σ R) (x : σ → Fin 2) :
    eval (x : σ → R) p = eval (x : σ → R) (MLE p.toEvalsZeroOne) := by
  simp only [MLE_eval_zeroOne, toEvalsZeroOne]

section DegreeOf

omit [Fintype σ] in
theorem singleEqPolynomial_degreeOf (r : R) (i j : σ) :
    degreeOf i (singleEqPolynomial r (X j)) ≤ if i = j then 1 else 0 := by
  rw [singleEqPolynomial_nf]
  calc
    _ ≤ max (degreeOf i ((2 * C r - 1) * X j)) (degreeOf i (1 - C r)) := by
      exact degreeOf_add_le i _ _
    _ ≤ max (degreeOf i (2 * C r - 1) + degreeOf i (X j))
            (degreeOf i (1 - C r)) := by
      gcongr
      repeat exact degreeOf_mul_le i _ _
    _ = max (degreeOf i (C (2 * r - 1)) + degreeOf i (X j))
            (degreeOf i (C (1 - r))) := by
      congr
      · simp only [map_sub, map_mul, map_one, sub_left_inj]; congr
      · simp only [map_sub, map_one]
    _ = max (0 + degreeOf i (X j)) 0 := by
      congr <;>
      exact degreeOf_C (R := R) _ i
    _ ≤ max (0 + (if i = j then 1 else 0)) 0 := by
      gcongr
      by_cases h : i = j
      · simpa only [h] using degreeOf_X_le (R := R) j i
      · simpa only [h] using le_of_eq (degreeOf_X_of_ne (R := R) i j h)
    _ = if i = j then 1 else 0 := by norm_num

omit [DecidableEq σ] in
theorem eqPolynomial_mem_restrictDegree (r : σ → R) : (eqPolynomial r) ∈ R⦃≤ 1⦄[X σ] := by
  classical
  rw [mem_restrictDegree_iff_degreeOf_le]
  intro i
  calc
    _ ≤ ∑ j : σ, degreeOf i (singleEqPolynomial (r j) (X j)) := by
      exact degreeOf_prod_le i _ _
    _ ≤ ∑ j : σ, if i = j then 1 else 0 := by
      gcongr
      exact singleEqPolynomial_degreeOf _ _ _
    _ = 1 := by norm_num

omit [DecidableEq σ] in
theorem eqPolynomial_degreeOf (r : σ → R) (i : σ) : degreeOf i (eqPolynomial r) ≤ 1 := by
  apply (mem_restrictDegree_iff_degreeOf_le _ _).mp
  exact eqPolynomial_mem_restrictDegree r

theorem MLE_mem_restrictDegree (evals : (σ → Fin 2) → R) : (MLE evals) ∈ R⦃≤ 1⦄[X σ] := by
  classical
  rw [mem_restrictDegree_iff_degreeOf_le]
  intro i
  calc
    _ ≤ (@Finset.univ (σ → Fin 2) _).sup
          fun x => degreeOf i ((eqPolynomial (x : σ → R)) * C (evals x)) := by
      exact degreeOf_sum_le i _ _
    _ ≤ (@Finset.univ (σ → Fin 2) _).sup
          fun x => degreeOf i (eqPolynomial (x : σ → R)) + degreeOf i (C (evals x)) := by
      gcongr
      exact degreeOf_mul_le i _ _
    _ ≤ (@Finset.univ (σ → Fin 2) _).sup fun x => 1 + 0 := by
      gcongr <;>
      simp [eqPolynomial_degreeOf]
    _ ≤ 1 := by simp

theorem MLE_degreeOf (evals : (σ → Fin 2) → R) (i : σ) : degreeOf i (MLE evals) ≤ 1 := by
  apply (mem_restrictDegree_iff_degreeOf_le _ _).mp
  exact MLE_mem_restrictDegree evals

end DegreeOf

-- TODO: add lemmas about the uniqueness of multilinear polynomials up to evaluations on hypercube

variable [DecidableEq R] [IsDomain R]

omit [Fintype σ] [DecidableEq σ] [DecidableEq R] in
theorem is_multilinear_eq_iff_eq_evals_zeroOne (p : MvPolynomial σ R) (q : MvPolynomial σ R)
    [Finite σ]
    (hp : p ∈ R⦃≤ 1⦄[X σ]) (hq : q ∈ R⦃≤ 1⦄[X σ]) :
    p = q ↔ p.toEvalsZeroOne = q.toEvalsZeroOne := by
  classical
  letI := Fintype.ofFinite σ
  constructor <;> intro h
  · simp only [h]
  · unfold toEvalsZeroOne at h
    rw [mem_restrictDegree_iff_degreeOf_le] at hp hq
    let S : σ → Finset R := fun i => {0, 1}
    have hDegree : ∀ i, degreeOf i (p - q) < #(S i) := fun i => by
      have hSi : #(S i) = 2 := by simp [S]
      rw [hSi]
      apply Nat.lt_of_le_pred (by decide)
      apply le_trans (degreeOf_sub_le i _ _)
      simp [hp, hq]
    have hEval : ∀ x ∈ piFinset fun i => S i, eval (x : σ → R) (p - q) = 0 := fun x hx => by
      simp only [eval_sub, sub_eq_zero]
      have hx' : ∀ i, x i = 0 ∨ x i = 1 := by
        simpa [S] using hx
      let y : σ → Fin 2 := fun i => if x i = 0 then 0 else 1
      have : x = y := by
        ext i
        have := hx' i
        by_cases h : x i = 0 <;> simp_all [y]
      rw [this]
      apply funext_iff.mp at h
      exact h y
    suffices p - q = 0 by exact eq_of_sub_eq_zero this
    exact eq_zero_of_degreeOf_lt_card_of_eval_eq_zero S hDegree hEval

omit [DecidableEq R] in
theorem is_multilinear_iff_eq_evals_zeroOne {p : MvPolynomial σ R} :
    p ∈ R⦃≤ 1⦄[X σ] ↔ MLE p.toEvalsZeroOne = p := by
  classical
  constructor <;> intro h
  · refine (is_multilinear_eq_iff_eq_evals_zeroOne (MLE p.toEvalsZeroOne) p
      (MLE_mem_restrictDegree p.toEvalsZeroOne) h).mpr ?_
    unfold toEvalsZeroOne; simp only [MLE_eval_zeroOne]
  · rw [←h]
    exact MLE_mem_restrictDegree p.toEvalsZeroOne

/-- Equivalence between multilinear polynomials and their evaluations on the Boolean hypercube -/
def MLEEquiv : R⦃≤ 1⦄[X σ] ≃ ((σ → Fin 2) → R) where
  toFun := fun p x => MvPolynomial.eval (x : σ → R) p
  invFun := fun evals => ⟨MLE evals, MLE_mem_restrictDegree evals⟩
  left_inv := fun ⟨p, hp⟩ => by
    simp only [Subtype.mk.injEq]
    exact is_multilinear_iff_eq_evals_zeroOne.mp hp
  right_inv := fun evals => by simp only [MLE_eval_zeroOne]

def MLEEquivFin {n : ℕ} : R⦃≤ 1⦄[X (Fin n)] ≃ (Fin (2 ^ n) → R) :=
  Equiv.trans MLEEquiv (Equiv.piCongr finFunctionFinEquiv (fun _ => Equiv.refl _))

private noncomputable def substPlus {n : ℕ} [NeZero n] [Field R] (p : MvPolynomial (Fin n) R) :
    MvPolynomial (Fin n) R :=
  p.aeval (fun i ↦ if i = 0 then 1 else (MvPolynomial.X i : MvPolynomial (Fin n) R))

private noncomputable def substMinus {n : ℕ} [NeZero n] [Field R] (p : MvPolynomial (Fin n) R) :
    MvPolynomial (Fin n) R :=
  p.aeval (fun i ↦ if i = 0 then -1 else MvPolynomial.X i)

omit [CommRing R] [DecidableEq R] [IsDomain R] in
private lemma substPlus_mem_restrictDegree {n : ℕ} [NeZero n] [Field R]
    {p : MvPolynomial (Fin n) R} (hp : p ∈ restrictDegree (Fin n) R 1) :
    substPlus p ∈ restrictDegree (Fin n) R 1 := by
      have h_support : ∀ m ∈ p.support, ∀ i, m i ≤ 1 := by
        rwa [mem_restrictDegree] at hp;
      unfold substPlus;
      have h_monomial : ∀ m ∈ p.support, (MvPolynomial.monomial m (p.coeff m)).aeval (fun i => if i = 0 then 1 else (MvPolynomial.X i : MvPolynomial (Fin n) R)) ∈ restrictDegree (Fin n) R 1 := by
        intro m hm
        have h_monomial : (MvPolynomial.monomial m (p.coeff m)).aeval (fun i => if i = 0 then 1 else (MvPolynomial.X i : MvPolynomial (Fin n) R)) = MvPolynomial.monomial (m.erase 0) (p.coeff m) := by
          simp +decide [ MvPolynomial.monomial_eq, aeval_def ];
          simp +decide [ Finset.prod_ite, Finset.filter_ne', Finsupp.erase ];
        simp_all +decide [ mem_restrictDegree ];
        intro i; specialize h_support m hm i; by_cases hi : i = 0 <;> aesop;
      rw [ MvPolynomial.as_sum p ];
      convert Submodule.sum_mem _ h_monomial using 1;
      rw [ map_sum ]

omit [DecidableEq R] in
private lemma substMinus_mem_restrictDegree {n : ℕ} [NeZero n] [Field R]
    {p : MvPolynomial (Fin n) R} (hp : p ∈ restrictDegree (Fin n) R 1) :
    substMinus p ∈ restrictDegree (Fin n) R 1 := by
      have := substPlus_mem_restrictDegree hp; simp_all +decide [ substPlus, substMinus ] ;
      have h_subst : ∀ i : Fin n, (MvPolynomial.degreeOf i (MvPolynomial.bind₁ (fun i => if i = 0 then -1 else X i) p)) ≤ 1 := by
        intro i
        have h_subst : ∀ m ∈ p.support, (MvPolynomial.degreeOf i (MvPolynomial.bind₁ (fun i => if i = 0 then -1 else X i) (MvPolynomial.monomial m (p.coeff m)))) ≤ 1 := by
          intro m hm
          have h_deg : m i ≤ 1 := by
            have := hp; rw [ MvPolynomial.mem_restrictDegree ] at this; aesop;
          simp_all +decide [ MvPolynomial.bind₁_monomial ];
          refine' le_trans ( MvPolynomial.degreeOf_mul_le _ _ _ ) _ ; simp_all +decide [ MvPolynomial.degreeOf_C ];
          refine' le_trans ( MvPolynomial.degreeOf_prod_le _ _ _ ) _;
          refine' le_trans ( Finset.sum_le_sum fun j hj => _ ) _;
          use fun j => if j = i then m i else 0;
          · split_ifs <;> simp_all +decide [ MvPolynomial.degreeOf_eq_sup ];
            · interval_cases m 0 <;> simp_all +decide [ MvPolynomial.coeff_one ];
            · cases Nat.even_or_odd ( m 0 ) <;> simp_all +decide [ pow_add, pow_mul ]; all_goals simp +decide [ MvPolynomial.coeff_one ];
            · simp +decide [ MvPolynomial.coeff_X_pow ];
            · rw [show 0 = ⊥ by rfl, Finset.sup_eq_bot_iff] 
              aesop (add simp [MvPolynomial.coeff_X_pow])
          · aesop;
        rw [ MvPolynomial.as_sum p ];
        rw [ map_sum ];
        exact le_trans ( MvPolynomial.degreeOf_sum_le _ _ _ ) ( Finset.sup_le fun m hm => h_subst m hm );
      simp_all +decide [ MvPolynomial.mem_restrictDegree ];
      intro s hs i; specialize h_subst i; rw [ MvPolynomial.degreeOf_eq_sup ] at h_subst; simp_all +decide [ Finset.sup_le_iff ] ;

omit [CommRing R] [DecidableEq R] [IsDomain R] in
private lemma mul_C_mem_restrictDegree {n : ℕ} [Field R]
    {p : MvPolynomial (Fin n) R} (hp : p ∈ restrictDegree (Fin n) R 1)
    (c : R) : p * C c ∈ restrictDegree (Fin n) R 1 := by
      convert Submodule.smul_mem _ c hp using 1;
      rw [ mul_comm, MvPolynomial.C_mul' ]

omit [DecidableEq R] in
private lemma even_mem {n : ℕ} [inst : Field R] [NeZero n] (p : R⦃≤ 1⦄[X (Fin n)]) :
    (substPlus p.1 + substMinus p.1) * C (2⁻¹) ∈ restrictDegree (Fin n) R 1 :=
  mul_C_mem_restrictDegree
    ((restrictDegree (Fin n) R 1).add_mem
    (substPlus_mem_restrictDegree p.2) (substMinus_mem_restrictDegree p.2)) _

private lemma odd_mem {n : ℕ} [inst : Field R] [NeZero n] (p : R⦃≤ 1⦄[X (Fin n)]) :
    (substPlus p.1 - substMinus p.1) * C (2⁻¹) ∈ restrictDegree (Fin n) R 1 :=
  mul_C_mem_restrictDegree
  ((restrictDegree (Fin n) R 1).sub_mem
    (substPlus_mem_restrictDegree p.2) (substMinus_mem_restrictDegree p.2)) _

noncomputable def even {n : ℕ} [Field R] [NeZero n] (p : R⦃≤ 1⦄[X (Fin n)]) :
  R⦃≤ 1⦄[X (Fin n)] :=
    ⟨(substPlus p.1 + substMinus p.1) * C (2⁻¹), even_mem p⟩

noncomputable def odd {n : ℕ} [Field R] [NeZero n] (p : R⦃≤ 1⦄[X (Fin n)]) :
  R⦃≤ 1⦄[X (Fin n)] :=
    ⟨(substPlus p.1 - substMinus p.1) * C (2⁻¹), odd_mem p⟩

omit [CommRing R] [DecidableEq R] in
private lemma formula_for_monomial {n : ℕ} [NeZero n] [Field R]
    (hchar : ¬CharP R 2)
    (m : Fin n →₀ ℕ) (c : R) (hm : ∀ i, m i ≤ 1) :
    (substPlus (monomial m c) + substMinus (monomial m c)) * C (2⁻¹) +
    X 0 * ((substPlus (monomial m c) - substMinus (monomial m c)) * C (2⁻¹)) = monomial m c := by
  have h2ne0 : (2 : R) ≠ 0 := 
    Ring.two_ne_zero (R := R) <| fun contra ↦ by
    rw [ringChar.eq_iff] at contra
    exact hchar contra
  -- Consider two cases: $m_0 = 0$ and $m_0 = 1$.
  by_cases h0 : m 0 = 0;
  · have h_subst : substPlus (MvPolynomial.monomial m c) = MvPolynomial.monomial m c ∧ substMinus (MvPolynomial.monomial m c) = MvPolynomial.monomial m c := by
      simp +decide [ substPlus, substMinus, h0 ];
      simp +decide [ MvPolynomial.bind₁_monomial, h0 ];
      simp +decide [ MvPolynomial.monomial_eq, Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', h0 ];
    simp [h_subst];
    rw [ ← two_smul R, smul_mul_assoc ];
    rw [ ← MvPolynomial.C_mul' ] ; ring ;
    rw [ mul_right_comm, ← MvPolynomial.C_mul, mul_inv_cancel₀ h2ne0, MvPolynomial.C_1, one_mul ];
  · have h_monomial : monomial m c = C c * X 0 * ∏ i ∈ m.support \ {0}, X i ^ (m i) := by
      rw [MvPolynomial.monomial_eq]
      simp +decide [ mul_assoc, Finsupp.prod] 
      have : (X 0 : R[X (Fin n)]) = X 0 ^ (m 0) := by simp [show m 0 = 1 by grind]
      rw [this,
          ←Finset.prod_eq_mul_prod_diff_singleton (s := m.support) 0 
            (f := fun i ↦ X i ^ m i) (by {
        intro hmem
        have : 0 ∈ m.support := by simp [h0]
        aesop
      })] 
      exact Or.inl <| by simp +decide
    -- Now substitute this into the expression.
    simp [h_monomial, substPlus, substMinus] at *; (
    simp +decide [ Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', h0 ] ; ring;
    simp +decide [ mul_assoc, ← mul_add ];
    erw [←map_mul, inv_mul_cancel₀ h2ne0] 
    aesop); -- Use `substPlus` and `substMinus` definitions.

private lemma formula_generic {n : ℕ} [NeZero n] [Field R] 
    (hchar : ¬CharP R 2)
    (p : MvPolynomial (Fin n) R) (hp : p ∈ restrictDegree (Fin n) R 1) :
    (substPlus p + substMinus p) * C (2⁻¹) +
    X 0 * ((substPlus p - substMinus p) * C (2⁻¹)) = p := by
  have h_expand : ∀ m ∈ p.support, (substPlus (monomial m (p.coeff m)) + substMinus (monomial m (p.coeff m))) * C (2⁻¹) + X 0 * ((substPlus (monomial m (p.coeff m)) - substMinus (monomial m (p.coeff m))) * C (2⁻¹)) = monomial m (p.coeff m) := by
    intro m hm
    apply formula_for_monomial hchar;
    rw [ mem_restrictDegree ] at hp
    aesop
  rw [ MvPolynomial.as_sum p ];
  convert Finset.sum_congr rfl h_expand using 1;
  simp +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, mul_add, mul_comm, substPlus, substMinus ];
  conv_lhs => rw [ MvPolynomial.as_sum p ];
  simp +decide only [map_sum, Finset.mul_sum _ _ _];
  simp +decide only [mul_sub, Finset.mul_sum _ _ _, Finset.sum_sub_distrib]

/-- The original formula `even_and_odd_formula` is false in characteristic 2 (where `2⁻¹ = 0`).
    This corrected version adds the hypothesis `[NeZero (2 : R)]` to ensure characteristic ≠ 2. -/
lemma even_and_odd_formula {n : ℕ} [Field R] [NeZero n]
    (hchar : ¬CharP R 2)
    {p : R⦃≤ 1⦄[X (Fin n)]} :
  (even p).1 + (MvPolynomial.X 0) * (odd p).1 = p.1 := by
  exact formula_generic hchar p.1 p.2
end MvPolynomial

end
