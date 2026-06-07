/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage

/-!
# Bad-scalar count adapters for repaired line-decoding coverage

This module routes the named repaired bad-scalar double-cover surface through the generic
finite-count lemmas in `MCABadCount.lean`.
-/

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators NNReal ENNReal

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The named repaired bad-scalar surface gives zero bad scalars via the generic
`∀ γ, ¬ mcaEvent` count lemma. -/
theorem mcaBadCount_eq_zero_of_badScalarDoubleCover_not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (hcov : ∀ γ : F,
      MCABadScalarDoubleCover (F := F) (A := A) C δ u₀ u₁ γ) :
    mcaBadCount (F := F) C δ u₀ u₁ = 0 :=
  mcaBadCount_eq_zero_of_forall_not_mcaEvent C δ u₀ u₁ fun γ =>
    MCABadScalarDoubleCover.not_mcaEvent C δ u₀ u₁ γ (hcov γ)

/-- The named repaired bad-scalar surface gives `ε_mca = 0` via the generic no-event
stack-count lemma. -/
theorem epsMCA_eq_zero_of_badScalarDoubleCover_not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := A) C δ (u 0) (u 1) γ) :
    epsMCA (F := F) C δ = 0 :=
  epsMCA_eq_zero_of_forall_not_mcaEvent C δ fun u γ =>
    MCABadScalarDoubleCover.not_mcaEvent C δ (u 0) (u 1) γ (hcov u γ)

set_option linter.style.longLine false in
#print axioms ProximityGap.mcaBadCount_eq_zero_of_badScalarDoubleCover_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.epsMCA_eq_zero_of_badScalarDoubleCover_not_mcaEvent

end

end ProximityGap
