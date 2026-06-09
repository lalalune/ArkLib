/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SumcheckCompletenessUncond
import ArkLib.ProofSystem.Logup.Security.LogupCompletenessClose

/-! # End-to-end LogUp completeness with the sum-check half internalized (#13)

`logup_completeness_full` (brick C) assembles the headline LogUp completeness from `hInit`,
`hSumcheck` (`SumcheckCompletenessResidual`), and `hAppend` (the outer⊕sum-check append). The
`hSumcheck` half is now supplied by `sumcheckCompletenessResidual_holds_uncondInner` — i.e. by the
proven `CubeFiber` / unconditional multi-round oracle completeness — modulo only the honest-support
condition. So the end-to-end completeness reduces to: the honest-support condition `hHonest`, the
standard data facts `hInit`/`hImplSupp`, and the genuine deep residual `hAppend` (the non-perfect
outer⊕sum-check append composition — the #433 challenge-seam core). -/

open OracleComp OracleSpec ProtocolSpec
namespace Logup
noncomputable section
variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
  [Fact ((-1 : F) ≠ 1)]
variable (n M : ℕ) (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **End-to-end LogUp completeness, sum-check half internalized via the proven `CubeFiber`.**
Reduced to: the honest-support condition `hHonest`, the standard data facts `hInit`/`hImplSupp`, and
the genuine deep append residual `hAppend`. The embedded-sum-check completeness is no longer a free
residual. -/
theorem logup_completeness_uncondSumcheck
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
        = support (liftM q : OracleComp oSpec β))
    (hAppend :
      AppendCompletenessResidual oSpec F n M params init impl
        (outerCompletenessResidual_of_neverFail oSpec F n M params init impl hInit)
        (sumcheckCompletenessResidual_holds_uncondInner oSpec F n M params init impl
          hHonest hInit hImplSupp)) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_full oSpec F n M params init impl hInit
    (sumcheckCompletenessResidual_holds_uncondInner oSpec F n M params init impl
      hHonest hInit hImplSupp)
    hAppend

end
end Logup
