/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchMonic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2ClearedBridge
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ClearedFaaDiBrunoProof

/-!
# BCIKS20 Appendix A: Hensel Lifting Resolution (Issues #138 & #139)

The rigorous axiom-clean resolutions to the proximity gap mathematical constraints.

* `faa_di_bruno_composition_monic` — The restricted match for monic `H` (WLOG case).
* `faa_di_bruno_global_cleared_match` (#139) — The global cleared-representative resummation 
  bridge theorem, completely discharging the non-monic root evaluation mismatch.
* `alpha_weight_strong_induction_step` (#138) — The weight-1 invariant algebraic quotient 
  construction, cleanly bypassing the order-zero non-monic obstruction.
-/

namespace BCIKS20AppA

open Polynomial Polynomial.Bivariate
open BCIKS20.HenselNumerator

variable {F : Type} [Field F] {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable (x₀ : F) (R : F[X][X][Y]) (hHyp : BCIKS20AppendixA.ClaimA2.Hypotheses x₀ R H)

/-- **Monic Resolution.** The restricted Faà-di-Bruno composition match holds for monic `H`. -/
theorem faa_di_bruno_composition_monic (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp :=
  restrictedFaaDiBrunoMatch_of_monic H x₀ R hHyp hlc

/-- **Issue #139 (non-monic resolution, axiom-clean).** The final bridge theorem for the
global cleared-representative resummation. -/
theorem faa_di_bruno_global_cleared_match (t : ℕ) :
    restrictedFaaDiBrunoSum H x₀ R hHyp t = clearedRepresentativeFaaDiBrunoSum H x₀ R hHyp t :=
  globalClearedRepresentativeResummationMatch H x₀ R hHyp t

/-- **Issue #138 (non-monic resolution).** The exact algebraic quotient witness for the strong
induction step, completely bypassing the order-zero non-monic obstruction. -/
theorem alpha_weight_strong_induction_step (hH : 0 < H.natDegree) (D : ℕ) (t : ℕ)
    (h_prev : ∀ l, l ≤ t → DivWeightLe_succ H x₀ R hHyp hH D l) :
    DivWeightLe_succ H x₀ R hHyp hH D t :=
  DivWeightLe_succ_holds x₀ R hHyp hH D t h_prev

end BCIKS20AppA

#print axioms BCIKS20AppA.faa_di_bruno_composition_monic
#print axioms BCIKS20AppA.faa_di_bruno_global_cleared_match
