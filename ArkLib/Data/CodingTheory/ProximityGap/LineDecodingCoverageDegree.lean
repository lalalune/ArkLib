/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.CoveragePigeonhole
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage

/-!
# Degree-cover adapters for repaired line decoding

`CoveragePigeonhole.lean` supplies the incidence-counting side of the GG25 multi-`γ` extraction:
large total agreement mass forces coordinates with many covering scalars.  This module connects
that degree language to the repaired #140 double-cover predicates from `LineDecodingCoverage.lean`.

The declarations here are deliberately local: a coordinate degree `> 1` gives two distinct
scalars, and pointwise degree `> 1` on a witness set gives `MCADoubleCoverOn`.  They do not
construct the Guruswami--Sudan cover or prove global `MCAForallDoubleCover`.
-/

namespace ProximityGap

open Finset
open NNReal Code
open scoped ProbabilityTheory BigOperators ENNReal

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

omit [Fintype ι] [Nonempty ι] [Field F] [DecidableEq F] in
/-- A coordinate with scalar-cover degree greater than one has two distinct covering scalars. -/
theorem exists_two_scalars_of_degree_gt_one
    (T : F → Finset ι) {i : ι}
    (hdeg : 1 < (Finset.univ.filter (fun a : F => i ∈ T a)).card) :
    ∃ a a' : F, a ≠ a' ∧ i ∈ T a ∧ i ∈ T a' := by
  rcases Finset.one_lt_card.mp hdeg with ⟨a, ha, a', ha', hne⟩
  simp only [mem_filter, mem_univ, true_and] at ha ha'
  exact ⟨a, a', hne, ha, ha'⟩

omit [Nonempty ι] [Field F] [DecidableEq F] in
/-- Total scalar-cover mass above `|ι|` produces at least one doubly covered coordinate. -/
theorem exists_coordinate_two_scalars_of_total_card_gt
    (T : F → Finset ι)
    (hmass : Fintype.card ι < ∑ a : F, (T a).card) :
    ∃ i : ι, ∃ a a' : F, a ≠ a' ∧ i ∈ T a ∧ i ∈ T a' := by
  rcases ArkLib.Coverage.exists_degree_gt (S := T) (k := 1) (by simpa using hmass)
      with ⟨i, hdeg⟩
  exact ⟨i, exists_two_scalars_of_degree_gt_one T hdeg⟩

/-- Pointwise scalar-cover degree `> 1` pins the pair on the whole witness set. -/
theorem pairJointAgreesOn_of_scalarCover_degree_gt_one
    (C : Set (ι → A)) (S : Finset ι) (u₀ u₁ v₁ v₂ : ι → A)
    (T : F → Finset ι)
    (hv₁ : v₁ ∈ C) (hv₂ : v₂ ∈ C)
    (hdeg : ∀ i ∈ S, 1 < (Finset.univ.filter (fun a : F => i ∈ T a)).card)
    (hagree : ∀ (a : F) (i : ι), i ∈ T a →
      v₁ i + a • v₂ i = u₀ i + a • u₁ i) :
    pairJointAgreesOn C S u₀ u₁ := by
  refine pairJointAgreesOn_of_double_cover (F := F) (A := A) C S u₀ u₁ v₁ v₂ hv₁ hv₂ ?_
  intro i hi
  rcases exists_two_scalars_of_degree_gt_one T (hdeg i hi) with ⟨a, a', hne, ha, ha'⟩
  exact ⟨a, a', hne, hagree a i ha, hagree a' i ha'⟩

omit [Fintype ι] [Nonempty ι] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- Convert pointwise scalar-cover degree `> 1` into the repaired local `MCADoubleCoverOn`
surface. -/
theorem MCADoubleCoverOn.of_scalarCover_degree_gt_one
    (C : Set (ι → A)) (S : Finset ι) (u₀ u₁ v₁ v₂ : ι → A)
    (T : F → Finset ι)
    (hv₁ : v₁ ∈ C) (hv₂ : v₂ ∈ C)
    (hdeg : ∀ i ∈ S, 1 < (Finset.univ.filter (fun a : F => i ∈ T a)).card)
    (hagree : ∀ (a : F) (i : ι), i ∈ T a →
      v₁ i + a • v₂ i = u₀ i + a • u₁ i) :
    MCADoubleCoverOn (F := F) C u₀ u₁ S := by
  refine ⟨v₁, hv₁, v₂, hv₂, ?_⟩
  intro i hi
  rcases exists_two_scalars_of_degree_gt_one T (hdeg i hi) with ⟨a, a', hne, ha, ha'⟩
  exact ⟨a, a', hne, hagree a i ha, hagree a' i ha'⟩

/-- A bad-event witness body contradicts pointwise scalar-cover degree `> 1` on that body. -/
theorem not_mcaEventBody_of_scalarCover_degree_gt_one
    (C : Set (ι → A)) (u₀ u₁ : ι → A) (S : Finset ι)
    {v₁ v₂ : ι → A} (T : F → Finset ι)
    (hv₁ : v₁ ∈ C) (hv₂ : v₂ ∈ C)
    (hpair : ¬ pairJointAgreesOn C S u₀ u₁)
    (hdeg : ∀ i ∈ S, 1 < (Finset.univ.filter (fun a : F => i ∈ T a)).card)
    (hagree : ∀ (a : F) (i : ι), i ∈ T a →
      v₁ i + a • v₂ i = u₀ i + a • u₁ i) :
    False :=
  hpair (pairJointAgreesOn_of_scalarCover_degree_gt_one C S u₀ u₁ v₁ v₂ T
    hv₁ hv₂ hdeg hagree)

end

end ProximityGap

#print axioms ProximityGap.exists_two_scalars_of_degree_gt_one
#print axioms ProximityGap.exists_coordinate_two_scalars_of_total_card_gt
set_option linter.style.longLine false in
#print axioms ProximityGap.pairJointAgreesOn_of_scalarCover_degree_gt_one
set_option linter.style.longLine false in
#print axioms ProximityGap.MCADoubleCoverOn.of_scalarCover_degree_gt_one
set_option linter.style.longLine false in
#print axioms ProximityGap.not_mcaEventBody_of_scalarCover_degree_gt_one
