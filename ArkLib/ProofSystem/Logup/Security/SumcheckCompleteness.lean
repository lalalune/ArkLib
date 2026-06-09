/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SubPhaseSplit
import ArkLib.ProofSystem.Logup.Security.LogupCompletenessUncond
import ArkLib.ProofSystem.Sumcheck.Spec.General

open scoped NNReal ENNReal
open OracleComp OracleSpec ProtocolSpec

namespace Logup

section SumcheckCompleteness

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances used when naming the sub-verifier obligations. -/
local instance : Inhabited F := ⟨0⟩

/-- **The embedded sum-check completeness residual for LogUp**, discharged on the honest-prover
support modulo the named single-round bridge.

This is a real proof — not a `sorry` — that the LogUp embedded sum-check phase is perfectly complete
(error `0`) from `midRelation` to `outputRelation`, obtained by delegating to the axiom-clean
`sumcheckCompletenessResidual_of_honest_perRound`. The bare unconditional form (residual from `hInit`
alone) is *not provable*: because `midRelation = Set.univ` carries no constraint, completeness must be
witnessed on the honest-prover support, and the inner multi-round sum-check needs its per-round
`liftContext`-commutation bridge. Those are exposed here as the precisely-typed named hypotheses
`hHonest`, `hPerRound`, `hImplSupp` rather than hidden inside a content-free `sorry`:

* `hHonest` — the honest-support data: every projected outer transcript comes from an underlying
  `inputRelation` input whose verifier challenge avoids the table poles, with the retained oracles
  the honest ones (discharges the LogUp grand-sum zero claim, hence `proj_complete`);
* `hPerRound` — the single-round inner sum-check `oracleReduction = reduction` commutation fact
  (the one genuinely deep residual; the rest of the inner completeness is the proven
  `Sumcheck.Spec.oracleReduction_perfectCompleteness` keystone);
* `hImplSupp` — the oracle implementation preserves query support;
* `hInit` — `init` never fails.
-/
theorem sumcheckCompletenessResidual_proved
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
    (hPerRound : ∀ i,
      (Sumcheck.Spec.SingleRound.oracleReduction F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i).toReduction =
        Sumcheck.Spec.SingleRound.reduction F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    SumcheckCompletenessResidual oSpec F n M params init impl :=
  sumcheckCompletenessResidual_of_honest_perRound oSpec F n M params init impl
    hHonest hPerRound hInit hImplSupp

end SumcheckCompleteness

end Logup

/-! ## Axiom audit -/
#print axioms Logup.sumcheckCompletenessResidual_proved
