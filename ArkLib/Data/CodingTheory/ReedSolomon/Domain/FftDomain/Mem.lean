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
lemma mem_def : x ∈ (ω : CosetFftDomain ι F) ↔ ∃ i, x = ω i := by aesop (add simp [Membership.mem])

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma mem_iff_exists_mul : 
  x ∈ ω ↔ ∃ i, x = ω.cosetGenerator * ω.subgroupDomain i := by
  aesop (add simp [Membership.mem])

omit [DecidableEq ι] in
lemma mem_toFinset_iff_exists_mul : 
  x ∈ ω.toFinset ↔ ∃ i, x = ω.cosetGenerator * ω.subgroupDomain i := by
  aesop (add simp [toFinset])

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp]
lemma mem_coset_domain_self {i : ι} :
  ω i ∈ ω := by simp [mem_def]

omit [DecidableEq ι] in
@[simp]
lemma mem_toFinset_iff_mem :
  x ∈ ω.toFinset ↔ x ∈ ω := by simp [mem_toFinset_iff_exists_mul, mem_iff_exists_mul]

omit [DecidableEq ι] in
@[simp high]
lemma mem_toFinset_self {i : ι} :
  ω i ∈ ω.toFinset := by simp [mem_toFinset_iff_mem]

end CosetFftDomain

instance {x : F} {ω : CosetFftDomain ι F} : Decidable (x ∈ ω) :=
  decidable_of_iff _ CosetFftDomain.mem_toFinset_iff_mem

end ReedSolomon
