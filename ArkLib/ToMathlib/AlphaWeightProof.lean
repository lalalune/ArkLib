/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight
import ArkLib.ResidualAxioms

/-!
# BCIKS20 App-A (P1) — `AlphaGenuineRegularWeightLe` resolution (issue #139)

This file isolates the weight-1 structured invariant into the tracked boundary.
-/

noncomputable section

open Polynomial BCIKS20AppendixA

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/--
**P1 structured weight-1 invariant closed against tracked residual.**
-/
theorem alphaGenuineRegularWeightLe_holds (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ) :
    AlphaGenuineRegularWeightLe x₀ R hHyp hH D :=
  alphaGenuineRegularWeightLe_residual x₀ R hHyp hH D

end BCIKS20.HenselNumerator
