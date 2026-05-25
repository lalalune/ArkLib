/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Field

import ArkLib.Data.CodingTheory.ReedSolomon.Domain.CosetFftDomain.Defs

namespace ReedSolomon 

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

structure FftDomain (ι : Type) [AddCommGroup ι]
  (F : Type) [Field F] extends CosetFftDomain ι F where
  cosetGenerator_one : cosetGenerator = 1 

namespace FftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
private lemma eq_iff_domains_eq {φ₁ φ₂ : FftDomain ι F} :
  φ₁ = φ₂ ↔ φ₁.subgroupDomain = φ₂.subgroupDomain := by
  rcases φ₁ with ⟨⟨f₁, _, x₁⟩, h₁⟩
  rcases φ₂ with ⟨⟨f₂, _, x₂⟩, h₂⟩
  aesop

end FftDomain

instance : FunLike (FftDomain ι F) ι F where
  coe fftDomain i := 
    fftDomain.subgroupDomain i
  coe_injective' φ₁ φ₂ h := by
    simp only [FftDomain.eq_iff_domains_eq]
    ext i
    have h := congrFun h i 
    simpa [Multiplicative.ofAdd] using h

namespace FftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma eval_fft_domain_eq_eval_domain
  {fftDomain : FftDomain ι F} {i : ι} :
  fftDomain i = fftDomain.subgroupDomain i := rfl

end FftDomain

instance : CosetFftDomainClass (FftDomain ι F) ι F where
  map_zero_unit ω := by 
    have : (0 : ι) = (1 : Multiplicative ι) := by rfl
    aesop (add simp [FftDomain.eval_fft_domain_eq_eval_domain])
  map_add ω i j := by 
    have : (0 : ι) = (1 : Multiplicative ι) := by rfl
    have : (i + j : ι) = (Multiplicative.ofAdd i) * (Multiplicative.ofAdd j) := by rfl
    aesop 
      (add simp [FftDomain.eval_fft_domain_eq_eval_domain])
  map_neg ω i := by sorry
  injective ω x y h := sorry

end ReedSolomon
