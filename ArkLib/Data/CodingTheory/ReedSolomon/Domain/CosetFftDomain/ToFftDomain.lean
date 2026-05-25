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
import ArkLib.Data.CodingTheory.ReedSolomon.Domain.FftDomain.Mem

namespace ReedSolomon

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

namespace CosetFftDomain

variable {ω : CosetFftDomain ι F} {x : F}

def toFftDomain (ω : CosetFftDomain ι F) : 
  FftDomain ι F where
  subgroupDomain := ω.subgroupDomain
  subgroupDomain_inj := ω.subgroupDomain_inj
  cosetGenerator := 1
  cosetGenerator_one := by rfl

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma mem_toFftDomain_iff_mul_mem :
  x ∈ ω.toFftDomain ↔ ω.cosetGenerator * x ∈ ω := by
  aesop (add simp [Multiplicative.ofAdd, mem_iff_exists_mul, FftDomain.mem_iff_exists])

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma mul_mem_of_mem_toFftDomain_of_mem {y : F}
  (hx : x ∈ ω.toFftDomain)
  (hy : y ∈ ω) :
  x * y ∈ ω := by
  simp_all only [FftDomain.mem_iff_exists, Multiplicative.exists, mem_iff_exists_mul]
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hx
  simp only [toFftDomain, Multiplicative.ofAdd, Equiv.coe_fn_mk]
  exists (a + b)
  have : a + b = Multiplicative.ofAdd a * Multiplicative.ofAdd b := by rfl
  aesop 
    (add simp [Multiplicative.ofAdd])
    (add safe (by field_simp))

end CosetFftDomain

end ReedSolomon
