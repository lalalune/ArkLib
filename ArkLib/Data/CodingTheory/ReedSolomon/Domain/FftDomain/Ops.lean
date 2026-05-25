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

import ArkLib.Data.CodingTheory.ReedSolomon.Domain.FftDomain.Mem
import ArkLib.Data.CodingTheory.ReedSolomon.Domain.CosetFftDomain.Ops

namespace ReedSolomon

variable {ι : Type} [AddCommGroup ι]
variable {F : Type} [Field F]

namespace FftDomain

variable {ω : FftDomain ι F} {i j : ι}

@[simp]
lemma apply_zero_eq_one {ω : FftDomain ι F} :
  ω 0 = 1 := by
  simp [eval_fft_domain_eq_eval_coset_fft_domain,
        CosetFftDomain.apply_zero,
        ω.cosetGenerator_one]

lemma apply_add_eq_mul :
  ω (i + j) = ω i * ω j := by
  simp 
    [eval_fft_domain_eq_eval_coset_fft_domain, 
      CosetFftDomain.apply_add_eq_inv_mul_mul,
      ω.cosetGenerator_one]

lemma mul_mem_of_mem
  {x₁ x₂ : F} (hx₁ : x₁ ∈ ω) (hx₂ : x₂ ∈ ω) :
  x₁ * x₂ ∈ ω := by 
  rw [mem_iff_exists] at *
  obtain ⟨⟨i₁, hi₁⟩, ⟨i₂, hi₂⟩⟩ := hx₁, hx₂
  exists (i₁ * i₂)
  aesop

@[simp]
lemma apply_neg_eq_inv : 
  ω (-i) = (ω i)⁻¹ := by
  have h_def : ω (-i) * ω i = 1 := by
    rw [←FftDomain.apply_add_eq_mul]
    aesop
  exact eq_inv_of_mul_eq_one_left h_def

lemma domain_sub_eq_div_domain {ω : FftDomain ι F}
  {i₁ i₂ : ι} :
  ω (i₁ - i₂) = ω i₁ / ω i₂ := by
  rw
    [sub_eq_add_neg,
      div_eq_mul_inv,
      FftDomain.apply_add_eq_mul,
      FftDomain.apply_neg_eq_inv]

section Smooth

@[simp]
lemma neg_one_mem_domain {n} [nz : NeZero n] {ω : SmoothFftDomain n F} :
  -1 ∈ ω := by
  have hn : n ≠ 0 := NeZero.ne _
  -- Let's denote this element as `k = 2^(i-1) : Fin (2^i)`.
  set k : Fin (2 ^ n) := ⟨2 ^ (n - 1), by
    exact pow_lt_pow_right₀ (by decide) (by omega)⟩
  generalize_proofs at *
  have h_order : (ω k) ^ 2 = 1 := by
    have hk_order : (ω k) ^ 2 = (ω (k + k)) := by aesop (add simp [sq, apply_add_eq_mul])
    convert hk_order using 1
    rw [show k + k = 0 by {
      rcases n with ⟨_ | n, hn⟩
        <;> norm_num [Fin.ext_iff, Fin.val_add, Fin.val_mul] at *
      ring_nf at *
      aesop
    }]
    aesop
  generalize_proofs at *
  (
  -- Since $k$ has additive order 2 in $\text{Fin}(2^i)$, we have $(ω.subdomain i k) \neq 1$.
  have h_ne_one : (ω k) ≠ 1 := by
    have h_ne_one : (ω k) ≠ ω 0 := by
      exact fun h ↦
        absurd
          (ω.injective h)
          (ne_of_gt <| Nat.lt_of_le_of_lt (Nat.zero_le _) <| pow_pos (by omega) _)
    generalize_proofs at *
    (
    exact fun h ↦ h_ne_one <| h.trans <| by simp )
  generalize_proofs at *
  (exact ⟨k, Or.resolve_left (sq_eq_one_iff.mp h_order) h_ne_one⟩))

end Smooth

end FftDomain

end ReedSolomon
