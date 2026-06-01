/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.CharP.Basic

import CompPoly.Data.MvPolynomial.Notation
import ArkLib.Data.MvPolynomial.Interpolation

namespace MvPolynomial

open BigOperators Fintype Finset

universe u

variable {σ : Type*} {R : Type*}

variable [Field R]
variable {n : ℕ} [NeZero n]
variable {p : MvPolynomial (Fin n) R}

private noncomputable def substPlus (p : MvPolynomial (Fin n) R) :
  MvPolynomial (Fin (n - 1)) R := p.aeval <| fun i ↦ 
  if h : i = 0 then 1 else MvPolynomial.X ⟨i.val - 1, by omega⟩ 

private noncomputable def substMinus (p : MvPolynomial (Fin n) R) : 
  MvPolynomial (Fin (n - 1)) R := p.aeval <| 
  fun i ↦ if h : i = 0 then -1 else MvPolynomial.X ⟨i.val - 1, by omega⟩

private lemma substPlus_mem_restrictDegree
  (hp : p ∈ restrictDegree (Fin n) R 1) :
  substPlus p ∈ restrictDegree (Fin (n - 1)) R 1 := by sorry 

private lemma substMinus_mem_restrictDegree
  (hp : p ∈ restrictDegree (Fin n) R 1) :
  substMinus p ∈ restrictDegree (Fin (n - 1)) R 1 := by sorry

omit [NeZero n] in
private lemma mul_C_mem_restrictDegree
  (hp : p ∈ restrictDegree (Fin n) R 1) (c : R) : 
  p * C c ∈ restrictDegree (Fin n) R 1 := by
  convert Submodule.smul_mem _ c hp using 1
  rw [mul_comm, MvPolynomial.C_mul']

private lemma even_mem (p : R⦃≤ 1⦄[X (Fin n)]) :
  (substPlus p.1 + substMinus p.1) * C (2⁻¹) ∈ restrictDegree (Fin (n - 1)) R 1 :=
  mul_C_mem_restrictDegree
    ((restrictDegree (Fin (n - 1)) R 1).add_mem
    (substPlus_mem_restrictDegree p.2) (substMinus_mem_restrictDegree p.2)) _

private lemma odd_mem (p : R⦃≤ 1⦄[X (Fin n)]) :
  (substPlus p.1 - substMinus p.1) * C (2⁻¹) ∈ restrictDegree (Fin (n - 1)) R 1 :=
  mul_C_mem_restrictDegree
  ((restrictDegree (Fin (n - 1)) R 1).sub_mem
    (substPlus_mem_restrictDegree p.2) (substMinus_mem_restrictDegree p.2)) _

noncomputable def even (p : R⦃≤ 1⦄[X (Fin n)]) :
  R⦃≤ 1⦄[X (Fin (n - 1))] :=
  ⟨(substPlus p.1 + substMinus p.1) * C (2⁻¹), even_mem p⟩

noncomputable def odd (p : R⦃≤ 1⦄[X (Fin n)]) :
  R⦃≤ 1⦄[X (Fin (n - 1))] :=
  ⟨(substPlus p.1 - substMinus p.1) * C (2⁻¹), odd_mem p⟩

private lemma formula_for_monomial (hchar : ¬CharP R 2)
  (m : Fin n →₀ ℕ) (c : R) (hm : ∀ i, m i ≤ 1) :
  (substPlus (monomial m c) + substMinus (monomial m c)).aeval 
    (fun i ↦ X (⟨i.val + 1, by omega⟩ : Fin n))
    * C (2⁻¹) +
  X 0 * ((substPlus (monomial m c) - substMinus (monomial m c)).aeval
    (fun i ↦ X (⟨i.val + 1, by omega⟩ : Fin n))
    * C (2⁻¹)) = monomial m c := by
  have h2ne0 : (2 : R) ≠ 0 := by
    simp_all [Nat.prime_two, CharP.charP_iff_prime_eq_zero]
  sorry

private lemma formula_generic
  (hchar : ¬CharP R 2)
  (p : MvPolynomial (Fin n) R) (hp : p ∈ restrictDegree (Fin n) R 1) :
  (substPlus p + substMinus p).aeval 
    (fun i ↦ X (⟨i.val + 1, by omega⟩ : Fin n)) * C (2⁻¹) +
  X 0 * ((substPlus p - substMinus p).aeval
    (fun i ↦ X (⟨i.val + 1, by omega⟩ : Fin n)) * C (2⁻¹)) = p := by
  sorry
  
/-- The original formula `even_and_odd_formula` is false in characteristic 2 (where `2⁻¹ = 0`).
    This corrected version adds the hypothesis `[NeZero (2 : R)]` to ensure characteristic ≠ 2. -/
lemma even_and_odd_formula (hchar : ¬CharP R 2)
  {p : R⦃≤ 1⦄[X (Fin n)]} :
  (even p).1.aeval (fun i ↦ X (⟨i.val + 1, by omega⟩ : Fin n)) + 
    (MvPolynomial.X 0) * (odd p).1.aeval (fun i ↦ X (⟨i.val + 1, by omega⟩ : Fin n)) = p.1 := by
  aesop 
    (add simp [even, odd])
    (add safe forward [formula_generic])

end MvPolynomial
