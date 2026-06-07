/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.Bridge2BGKS20

/-!
# BGKS20 All-But-One Scalar Bridge

This module adds a small producer for the `CodingTheory.Bridge.NearCertainBadLine` residual used
by the BGKS20 characteristic-2 separation bridge.

The paper-level construction still has to provide a stack `u` that is not jointly close to the
code and a single exceptional scalar `γ_bad`. Once those are known, this file packages the
"all scalars except `γ_bad` are close" statement into the counted-good-set form expected by
`NearCertainBadLine`, taking the good set to be `Finset.univ.erase γ_bad`.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory.Bridge

open scoped NNReal BigOperators
open ProximityGap Code

section AllButOne

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- Package an "all but one scalar" BGKS20-style witness as a `NearCertainBadLine`.

Given a stack `u` that is not jointly `δ_int`-close to `C`, if every scalar except a distinguished
`γ_bad` produces a line point within `δ_fld` of `C`, then the good combiner set
`Finset.univ.erase γ_bad` has size `|F| - 1` and supplies the counted witness required by
`NearCertainBadLine`.

This is only Finset-cardinality glue around the existing residual predicate; it does not construct
the BGKS20 characteristic-2 stack. -/
theorem nearCertainBadLine_of_allButOne
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) (u : WordStack A (Fin 2) ι)
    (γ_bad : F)
    (hjp : ¬ jointProximity (C := C) (u := u) δ_int)
    (hclose : ∀ γ : F, γ ≠ γ_bad → δᵣ(u 0 + γ • u 1, C) ≤ δ_fld) :
    NearCertainBadLine (F := F) (A := A) C δ_fld δ_int := by
  classical
  refine ⟨u, hjp, Finset.univ.erase γ_bad, ?_, ?_⟩
  · intro γ hγ
    exact hclose γ (Finset.mem_erase.mp hγ).1
  · have hcard_eq : (Finset.univ.erase γ_bad).card = Fintype.card F - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ γ_bad), Finset.card_univ]
    have hpos : 0 < Fintype.card F := Fintype.card_pos
    have hone : 1 ≤ Fintype.card F := Nat.succ_le_of_lt hpos
    have hcard_real : ((Finset.univ.erase γ_bad).card : ℝ) =
        (Fintype.card F : ℝ) - 1 := by
      rw [hcard_eq, Nat.cast_sub hone]
      norm_num
    exact le_of_eq hcard_real.symm

/-- The BGKS20 separation endpoint from an "all but one scalar" witness. -/
theorem epsCA_separation_bridge_of_allButOne
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) (u : WordStack A (Fin 2) ι)
    (γ_bad : F)
    (hjp : ¬ jointProximity (C := C) (u := u) δ_int)
    (hclose : ∀ γ : F, γ ≠ γ_bad → δᵣ(u 0 + γ • u 1, C) ≤ δ_fld) :
    ENNReal.ofReal (1 - 1 / Fintype.card F) ≤ epsCA (F := F) (A := A) C δ_fld δ_int :=
  epsCA_separation_bridge_of_residual (F := F) (A := A) C δ_fld δ_int
    (nearCertainBadLine_of_allButOne C δ_fld δ_int u γ_bad hjp hclose)

end AllButOne

end CodingTheory.Bridge

/-! ### Axiom audit (issue #22 all-but-one bridge surface) -/

#print axioms CodingTheory.Bridge.nearCertainBadLine_of_allButOne
#print axioms CodingTheory.Bridge.epsCA_separation_bridge_of_allButOne
