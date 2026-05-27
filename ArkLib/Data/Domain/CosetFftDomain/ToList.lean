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

import ArkLib.Data.Domain.CosetFftDomain.Mem
import ArkLib.Data.Domain.FftDomain.Mem

namespace Domain

variable {ι : Type} [Fintype ι] [AddCommGroup ι]
variable {F : Type} [Field F] [DecidableEq F]

namespace CosetFftDomainClass

variable {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]

noncomputable def toList (ω : D) : List (toFinset ω) :=
  Finset.toListWithProof <| toFinset ω

set_option linter.unusedSimpArgs false in -- false alert
lemma toList_eq_finset_toList {ω : D} :
  (toList ω).map (fun x ↦ x.1) = (toFinset ω).toList := by simp [toList, mem_def]

end CosetFftDomainClass

namespace CosetFftDomain 

noncomputable abbrev toList (ω : CosetFftDomain ι F) : List ω.toFinset :=
  CosetFftDomainClass.toList ω

end CosetFftDomain

namespace FftDomain

noncomputable abbrev toList (ω : FftDomain ι F) : List ω.toFinset :=
  CosetFftDomainClass.toList ω

end FftDomain

end Domain
