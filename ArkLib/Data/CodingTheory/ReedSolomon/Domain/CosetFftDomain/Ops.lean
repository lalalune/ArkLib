/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Field

import ArkLib.Data.CodingTheory.ReedSolomon.Domain.CosetFftDomain.Mem

namespace ReedSolomon

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

namespace CosetFftDomain

variable {ω : CosetFftDomain ι F} {i j : ι}

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma apply_zero : ω 0 = ω.cosetGenerator := by 
  have : (0 : ι) = (1 : Multiplicative ι) := by rfl
  aesop (add simp
     [eval_coset_fft_domain_eq_eval_generator_mul_domain])

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma apply_add_eq_inv_mul_mul :
  ω (i + j) = ω.cosetGenerator⁻¹ * ω i * ω j := by cases ω with
  | mk x ω =>
    have : i + j = Multiplicative.ofAdd i * Multiplicative.ofAdd j := by rfl
    aesop
      (add simp 
        [eval_coset_fft_domain_eq_eval_generator_mul_domain, ]) (add safe (by ring_nf))

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma apply_neg_eq_sq_mul_inv :
  ω (-i) = ω.cosetGenerator ^ 2 * (ω i)⁻¹ := by cases ω with
  | mk x ω =>
  have : -i = (Multiplicative.ofAdd i)⁻¹ := by rfl 
  aesop 
    (add simp [eval_coset_fft_domain_eq_eval_generator_mul_domain]) 
    (add safe (by field_simp))

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma apply_sub_eq_mul_div :
  ω (i - j) = ω.cosetGenerator * ω i / ω j := by cases ω with
  | mk x ω =>
  have : (i - j) = Multiplicative.ofAdd i / Multiplicative.ofAdd j := by rfl
  aesop 
    (add simp [eval_coset_fft_domain_eq_eval_generator_mul_domain, Multiplicative.ofAdd]) 
    (add safe (by field_simp))

end CosetFftDomain

end ReedSolomon
