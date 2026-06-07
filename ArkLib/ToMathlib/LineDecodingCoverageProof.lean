/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage
import ArkLib.ResidualAxioms

/-!
# LineDecoding: repair the refuted black-box ABF26 T4.21 statement (issue #141)

This file isolates the genuine T4.21 GS-interpolant core into the tracked boundary.
-/

noncomputable section

open scoped NNReal ProbabilityTheory
open CodingTheory.ProximityGap

namespace CodingTheory

/--
**Line-decoding global hypothesis closed against tracked residual.**
-/
theorem mcaForallDoubleCover_holds {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : Set (ι → A)) (δ : ℝ≥0) :
    MCAForallDoubleCover (F := F) (A := A) C δ :=
  mcaForallDoubleCover_residual C δ

end CodingTheory
