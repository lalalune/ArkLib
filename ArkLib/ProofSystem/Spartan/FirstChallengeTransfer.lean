/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.FirstChallengeComplete
import ArkLib.ProofSystem.Spartan.FirstChallengeCoherent
import ArkLib.OracleReduction.LiftContext.OracleReduction

/-!
# First sum-check completeness transfer (issue #114)

The Spartan first sum-check `oracleReduction.firstChallenge` is the `liftContext` of the generic
`RandomQuery` oracle reduction onto the virtual zero-check polynomial `𝒢`. This module transfers the
proven `RandomQuery` perfect completeness through that lift, using the two side conditions already
established:

* the coherence instance `firstChallenge_liftContextCoherent` (the #433 framework obligation), and
* the value-level lens completeness `firstChallenge_isComplete` (R1CS-satisfying instances project
  to the `RandomQuery` input relation `𝒢 = 0` and lift back to the preserved R1CS output relation).

`firstChallenge_perfectCompleteness` then follows by `OracleReduction.liftContext_perfectCompleteness`
(`hStmt = rfl`, since both lenses share `firstChallengeStmtLens`) applied to
`RandomQuery.oracleReduction_completeness`. This is the first fully-complete sub-protocol of the
Spartan PIOP.
-/

open MvPolynomial OracleSpec OracleComp

namespace Spartan.Spec

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R]
    (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι) [SampleableType R]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **First sum-check completeness transfer.** The `firstChallenge` oracle reduction is perfectly
complete from the R1CS input relation `fcRelIn` to the (preserved) R1CS output relation `fcRelOut`. -/
theorem firstChallenge_perfectCompleteness :
    (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl
      (fcRelIn R pp) (fcRelOut R pp) := by
  unfold oracleReduction.firstChallenge
  haveI : OracleVerifier.LiftContextCoherent (firstChallengeOracleLens R pp oSpec)
      (RandomQuery.oracleReduction oSpec (MvPolynomial (Fin pp.ℓ_m) R)).verifier :=
    firstChallenge_liftContextCoherent (R := R) pp oSpec
  haveI : Context.Lens.IsComplete (fcRelIn R pp)
      (RandomQuery.relIn (MvPolynomial (Fin pp.ℓ_m) R)) (fcRelOut R pp)
      (RandomQuery.relOut (MvPolynomial (Fin pp.ℓ_m) R))
      ((RandomQuery.oracleReduction oSpec (MvPolynomial (Fin pp.ℓ_m) R)).toReduction.compatContext
        (firstChallengeContextLens R pp).toContext)
      (firstChallengeContextLens R pp).toContext :=
    firstChallenge_isComplete R pp _
  exact OracleReduction.liftContext_perfectCompleteness rfl
    (RandomQuery.oracleReduction_completeness (oSpec := oSpec)
      (OStatement := MvPolynomial (Fin pp.ℓ_m) R))

end Spartan.Spec
