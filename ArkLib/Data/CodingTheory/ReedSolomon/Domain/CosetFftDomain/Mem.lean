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
import ArkLib.ToMathlib.Finset.ToListWithProof

namespace ReedSolomon

open Function

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

instance {D : Type}
  [FunLike D ι F] [CosetFftDomainClass D ι F] : Membership F D where
  mem φ x := ∃ i, φ i = x

namespace CosetFftDomain

def toFinset (ω : CosetFftDomain ι F) : Finset F :=
  Finset.image ω Finset.univ

instance
    {ι : Type} [AddCommGroup ι] [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F] :
  CoeSort (CosetFftDomain ι F) Type where
    coe d := toFinset d

end CosetFftDomain

instance {ω : CosetFftDomain ι F} : Inhabited ω.toFinset where
  default := ⟨ω 0, by simp [CosetFftDomain.toFinset]⟩

instance {ω : CosetFftDomain ι F} : Inhabited ω where
  default := ⟨ω 0, by simp [CosetFftDomain.toFinset]⟩

namespace CosetFftDomain

variable {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F] {ω : D}
variable {x : F}

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma mem_def : x ∈ ω ↔ ∃ i, x = ω i := by aesop (add simp [Membership.mem])

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp]
lemma mem_self {i : ι} :
  ω i ∈ ω := by simp [mem_def]

end CosetFftDomain

namespace CosetFftDomain

variable {ω : CosetFftDomain ι F} {x : F}

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma mem_iff_exists_mul : 
  x ∈ ω ↔ ∃ i, x = ω.cosetGenerator * ω.subgroupDomain i := by
  aesop (add simp [Membership.mem])

omit [DecidableEq ι] in
lemma mem_toFinset_iff_exists_mul : 
  x ∈ ω.toFinset ↔ ∃ i, x = ω.cosetGenerator * ω.subgroupDomain i := by
  aesop (add simp [toFinset])

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
