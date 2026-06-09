/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.OracleCompletenessUncondCorrect
import ArkLib.ProofSystem.Logup.Security.SumcheckCompletenessClose
import ArkLib.ProofSystem.Logup.Security.SumcheckLensProjComplete

/-! # LogUp embedded sum-check completeness — `hInner` discharged via the proven `CubeFiber` (#13)

Brick B (`sumcheckCompletenessResidual_holds`) reduced `SumcheckCompletenessResidual` to two
residuals: `hProj` (the honest-support `proj_complete` algebra) and `hInner` (the inner multi-round
sum-check ORACLE perfect completeness). Both are now discharged:
* `hInner` ← `Sumcheck.Spec.oracleReduction_perfectCompleteness_unconditional` — the bridge-free
  multi-round oracle completeness, whose only residual (the per-round lens coherence) is the proven
  `CubeFiber`. `logupConcreteSumcheckOracleReduction = Sumcheck.Spec.oracleReduction …` and
  `innerSumcheckRelIn/Out = relationRound 0/last`, all definitionally, so it plugs in on the nose.
* `hProj` ← `SumcheckLensProjComplete_holds_of_honest` (RA) on the honest-prover support.

So `SumcheckCompletenessResidual` holds modulo only the honest-support condition `hHonest` and the
standard data facts `hInit`/`hImplSupp`. -/

open OracleComp OracleSpec ProtocolSpec
namespace Logup
noncomputable section
variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
  [Fact ((-1 : F) ≠ 1)]
variable (n M : ℕ) (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **`SumcheckCompletenessResidual`, with `hInner` discharged via the proven `CubeFiber`.** Reduced
to only the honest-support condition `hHonest` (what completeness asserts on the honest run) plus the
standard data facts. The inner multi-round sum-check oracle completeness is no longer a residual. -/
theorem sumcheckCompletenessResidual_holds_uncondInner
    (hHonest :
      ∀ (stmtIn : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)),
        ∃ (stmtIn₀ : StmtIn F n M) (oStmtIn₀ : ∀ i, OStmtIn F n M i),
          (((stmtIn₀, oStmtIn₀), ()) ∈ inputRelation F n M) ∧
          (∀ u : Hypercube n,
            stmtIn.1.xChallenge + evalOnHypercube (tableOracle oStmtIn₀) u ≠ 0) ∧
          stmtIn.2 =
            (fun
              | .input i => oStmtIn₀ i
              | .multiplicity => honestMultiplicity oStmtIn₀
              | .helpers => honestHelpers params oStmtIn₀ stmtIn.1.xChallenge))
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    SumcheckCompletenessResidual oSpec F n M params init impl :=
  sumcheckCompletenessResidual_holds oSpec F n M params init impl
    (SumcheckLensProjComplete_holds_of_honest F n M params hHonest)
    (Sumcheck.Spec.oracleReduction_perfectCompleteness_unconditional hInit hImplSupp)

end
end Logup
