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

import ArkLib.Data.CodingTheory.ReedSolomon.Domain.CosetFftDomain.Subdomain
import ArkLib.Data.CodingTheory.ReedSolomon.Domain.FftDomain.Ops
import ArkLib.Data.CodingTheory.ReedSolomon.Domain.FftDomain.ToSubgroup

namespace ReedSolomon

variable {F : Type} [Field F]

namespace FftDomainClass

variable {n : ℕ}
variable {D : Type} [FunLike D (Fin (2 ^ n)) F] [FftDomainClass D (Fin (2 ^ n)) F]
variable {ω : D} {x : F}

open CosetFftDomainClass

def subdomain (ω : D) (i : ℕ) : SmoothFftDomain (n - i) F := 
  (CosetFftDomainClass.subdomain ω i).toFftDomain

lemma mem_fft_subdomain_iff_mem_coset_subdomain {i : ℕ} :
  x ∈ subdomain ω i ↔ x ∈ CosetFftDomainClass.subdomain ω i := by
  simp [subdomain, mem_toFftDomain_iff_mul_mem, CosetFftDomain.map_0_eq_coset_generator]

lemma mem_subdomain_of_mem_subdomain_of_le {i j : ℕ} (h : x ∈ subdomain ω i) (hji : j ≤ i) :
  x ∈ subdomain ω j := by 
    aesop 
      (add simp [mem_fft_subdomain_iff_mem_coset_subdomain])
      (add unsafe forward [mem_subdomain_of_le_of_mem_subdomain])

lemma subdomain_toFinset_subset_subdomain_toFinset_of_le [DecidableEq F]
  {i j : ℕ} (hji : j ≤ i) :
  (subdomain ω i).toFinset ⊆ (subdomain ω j).toFinset := fun x hx ↦ by
  aesop (add unsafe [mem_subdomain_of_mem_subdomain_of_le])

lemma subdomain_toSubgroup_subset_subdomain_toSubgroup_of_le [DecidableEq F]
  {i j : ℕ} (hji : j ≤ i) :
  (subdomain ω i).toSubgroup ≤ (subdomain ω j).toSubgroup := fun x hx ↦ by
  aesop (add unsafe [mem_subdomain_of_mem_subdomain_of_le])

end FftDomainClass

namespace CosetFftDomainClass

lemma mem_subdomain_of_mem_subdomain_of_mem_fft_subdomain {n : ℕ}
  {D : Type} [FunLike D (Fin (2 ^ n)) F] [CosetFftDomainClass D (Fin (2 ^ n)) F]
  {ω : D} {i j : ℕ} (hji : j ≤ i) (hn : i ≤ n)
  {a b : F}
  (ha : a ∈ subdomain ω i)
  (hb : b ∈ FftDomainClass.subdomain (toFftDomain ω) j) :
  a * b ∈ subdomain ω i := by sorry


end CosetFftDomainClass

namespace FftDomain 

abbrev subdomain {n : ℕ} (ω : SmoothFftDomain n F) (i : ℕ) : SmoothFftDomain (n - i) F :=
  FftDomainClass.subdomain ω i

end FftDomain

end ReedSolomon
