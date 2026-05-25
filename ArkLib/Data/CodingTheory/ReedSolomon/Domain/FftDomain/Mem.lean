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
 
import ArkLib.Data.CodingTheory.ReedSolomon.Domain.CosetFftDomain.Mem
import ArkLib.Data.CodingTheory.ReedSolomon.Domain.FftDomain.Defs
import ArkLib.ToMathlib.Finset.ToListWithProof

namespace ReedSolomon

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

namespace FftDomain

open CosetFftDomain

variable {ω : FftDomain ι F} {x : F}

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma mem_iff_exists :
  x ∈ ω ↔ ∃ i, x = ω.subgroupDomain i := by
  aesop (add simp [Membership.mem])

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma mem_iff_mem_toCosetFftDomain :
  x ∈ ω ↔ x ∈ ω.toCosetFftDomain := by
  simp [mem_iff_exists, mem_iff_exists_mul, ω.cosetGenerator_one]

omit [DecidableEq ι] in
lemma mem_toFinset_iff_exists : 
  x ∈ ω.toFinset ↔ ∃ i, x = ω.subgroupDomain i := by
  rw [CosetFftDomain.mem_toFinset_iff_exists_mul, 
      ω.cosetGenerator_one]
  aesop 

omit [DecidableEq ι] in
@[simp]
lemma mem_toFinset_iff_mem :
  x ∈ ω.toFinset ↔ x ∈ ω := by 
  rw [CosetFftDomain.mem_toFinset_iff_mem,
      mem_iff_mem_toCosetFftDomain]

omit [DecidableEq ι] in
@[simp high]
lemma mem_toFinset_self {i : ι} :
  ω i ∈ ω.toFinset := by 
  simp [CosetFftDomain.mem_toFinset_iff_mem, ←mem_iff_mem_toCosetFftDomain]

end FftDomain

instance {x : F} {ω : FftDomain ι F} : Decidable (x ∈ ω) :=
  decidable_of_iff _ FftDomain.mem_toFinset_iff_mem

end ReedSolomon
