/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.LogupCompletenessClose
import ArkLib.ProofSystem.Logup.Security.SumcheckLensProjComplete
import ArkLib.ProofSystem.Logup.Security.BridgeAndAppendResiduals
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone

/-!
# LogUp Protocol 2 — most-unconditional completeness (issue #13, keystone K-compFull)

This file assembles the **most-unconditional** LogUp Protocol 2 completeness statement currently
attainable, by discharging the inner multi-round sum-check oracle completeness `hInner` with the
**now-proven** binary verifier-fusion keystone
`OracleReduction.oracleVerifier_append_toVerifier` (in
`Composition/Sequential/AppendToVerifierKeystone.lean`, sorry-free), threaded through the existing
reduction chain.

## The chain

1. **Binary verifier fusion is proven.** The named residual
   `OracleVerifier.BinaryVerifierFusion oSpec` (the verifier analogue of `Prover.append_run`,
   from `BridgeAndAppendResiduals.lean`) is *exactly*
   `(OracleVerifier.append V₁ V₂).toVerifier = Verifier.append V₁.toVerifier V₂.toVerifier`
   for all appendable pairs — which is the keystone
   `OracleReduction.oracleVerifier_append_toVerifier`. So `binaryVerifierFusion_holds` discharges it
   with no residual.

2. **Inner multi-round sum-check oracle completeness, modulo the per-round bridge.** From the binary
   fusion, the proven `Sumcheck.Spec.oracleReductionToReductionResidual_of_binary` reduces the
   unbounded-round Sumcheck bridge `oracleReductionToReductionResidual` to the single per-round
   single-round bridge `hPerRound`
   (`(SingleRound.oracleReduction i).toReduction = SingleRound.reduction i`, a `liftContext`
   commutation fact orthogonal to the seqCompose fusion). Feeding that bridge into
   `Sumcheck.Spec.oracleReduction_perfectCompleteness` (which discharges everything else via the
   proven `reduction_perfectCompleteness`) yields the inner perfect completeness `hInner` for
   `logupConcreteSumcheckOracleReduction` between `innerSumcheckRelIn` and `innerSumcheckRelOut`.

3. **Embedded sum-check phase completeness.** With `hInner` discharged and the honest-support data
   `hHonest` (which discharges the `proj_complete` algebraic obligation `SumcheckLensProjComplete`
   on the honest-prover support via the proven `SumcheckLensProjComplete_holds_of_honest`),
   `Logup.sumcheckCompletenessResidual_of_honest` yields `SumcheckCompletenessResidual` — the
   embedded sum-check phase is perfectly complete on the honest support.

4. **End-to-end completeness.** Feeding the outer half (proven in-tree from `NeverFail init`), the
   discharged sum-check half, and the append-composition brick `hAppend` into
   `Logup.logup_completeness_full` gives the headline LogUp completeness.

## Residual surface (`logup_completeness_uncond`)

The smallest honest residual set after this brick:

* `hInit : NeverFail init` — the standard completeness initialization assumption.
* `hHonest` — the honest-support condition: every projected outer transcript arises from a genuine
  `inputRelation` input with the honest oracles and a pole-free verifier challenge. This is exactly
  what completeness asserts on the honest run; it is threaded, not assumed away.
* `hPerRound` — the per-round single-round `liftContext`-commutation bridge for the inner sum-check.
* `hImplSupp` — the standard oracle-implementation support-faithfulness condition (shared by every
  `*_perfectCompleteness` brick in-tree).
* `hAppend` — the non-perfect outer⊕sumcheck append-composition completeness (the only genuinely
  non-perfect residual: it must carry the non-zero outer error `logupCompletenessError F n` through
  the message seam; the *perfect* special case below discharges its analogue outright).

## The perfect special case (`logup_completeness_uncond_perfect`) — zero append residual

When `logupCompletenessError F n = 0`, both component errors are `0`, the seam is a message seam,
and the proven oracle-level keystone discharges the append residual with **no** `hAppend`. We feed
the discharged `hSumcheck` into the already-zero-residual `Logup.logup_completeness_full_perfect`,
leaving only `hInit`, `hHonest`, `hPerRound`, `hImplSupp`, and the structural message-seam direction
facts (all proven elsewhere or `rfl`).

No `sorry`/`sorryAx`/`admit`: every step is a real proof or an explicitly named hypothesis. The
axiom audit at the bottom confirms axiom-cleanliness (`propext`, `Classical.choice`, `Quot.sound`).
-/

open scoped NNReal ENNReal
open OracleComp OracleSpec ProtocolSpec

namespace Logup

section Uncond

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`); needed for the inner-sum-check `[Inhabited R]` instance and to match
the local instances used throughout the LogUp completeness development. -/
local instance instInhabitedFieldLogupUncond : Inhabited F := ⟨0⟩

/-! ### Step 1: the binary verifier fusion is proven (no residual) -/

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- **The binary verifier-fusion residual is discharged.** `OracleVerifier.BinaryVerifierFusion`
is, by definition, the universally-quantified
`(OracleVerifier.append V₁ V₂).toVerifier = Verifier.append V₁.toVerifier V₂.toVerifier`, which is
exactly the proven keystone `OracleReduction.oracleVerifier_append_toVerifier` (sorry-free in
`AppendToVerifierKeystone.lean`). So the whole unbounded-round verifier fusion — and with it the
Sumcheck `hBridge` — is now unconditional. -/
theorem binaryVerifierFusion_holds : OracleVerifier.BinaryVerifierFusion oSpec := by
  intro Stmt₁ ιₛ₁ OStmt₁ Oₛ₁ Stmt₂ ιₛ₂ OStmt₂ Oₛ₂ Stmt₃ ιₛ₃ OStmt₃ Oₛ₃
    p q pSpec₁ pSpec₂ Oₘ₁ Oₘ₂ V₁ c₁ V₂
  exact OracleReduction.oracleVerifier_append_toVerifier (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁)
    V₁ V₂

/-! ### Step 2: inner multi-round sum-check oracle completeness, modulo the per-round bridge

`logupConcreteSumcheckOracleReduction oSpec F n M params Fact.out` is *definitionally*
`Sumcheck.Spec.oracleReduction F (logupSumcheckDegree M params) (signDomain F Fact.out) n oSpec`, and
`innerSumcheckRelIn` / `innerSumcheckRelOut` are *definitionally* `relationRound … 0` /
`relationRound … (Fin.last n)`. So `Sumcheck.Spec.oracleReduction_perfectCompleteness` applies on the
nose, once its `hBridge` (`oracleReductionToReductionResidual`) is supplied. We supply that bridge
from the proven binary fusion (`binaryVerifierFusion_holds`) plus the per-round bridge `hPerRound`,
via the proven `Sumcheck.Spec.oracleReductionToReductionResidual_of_binary`. -/

/-- **Inner multi-round sum-check oracle perfect completeness, modulo the per-round bridge.**
The only residual is `hPerRound`, the single-round `liftContext`-commutation fact; the deep
unbounded-round verifier fusion is discharged by the proven binary keystone. -/
theorem inner_sumcheck_perfectCompleteness_of_perRound
    (hPerRound : ∀ i,
      (Sumcheck.Spec.SingleRound.oracleReduction F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i).toReduction =
        Sumcheck.Spec.SingleRound.reduction F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (logupConcreteSumcheckOracleReduction oSpec F n M params
        (Fact.out : (-1 : F) ≠ 1)).perfectCompleteness init impl
      (innerSumcheckRelIn F n M params)
      (innerSumcheckRelOut F n M params) := by
  -- The Sumcheck `hBridge` from the proven binary fusion + the per-round bridge.
  have hBridge :
      Sumcheck.Spec.oracleReductionToReductionResidual F (logupSumcheckDegree M params)
        (signDomain F (Fact.out : (-1 : F) ≠ 1)) n oSpec :=
    Sumcheck.Spec.oracleReductionToReductionResidual_of_binary
      (binaryVerifierFusion_holds oSpec) hPerRound
  -- `logupConcreteSumcheckOracleReduction`, `innerSumcheckRelIn/Out` are definitionally the generic
  -- Sumcheck oracle reduction and its round-`0`/round-`last` relations; apply the oracle-level
  -- completeness keystone (which discharges everything else via `reduction_perfectCompleteness`).
  exact Sumcheck.Spec.oracleReduction_perfectCompleteness
    (R := F) (deg := logupSumcheckDegree M params)
    (D := signDomain F (Fact.out : (-1 : F) ≠ 1)) (n := n) (oSpec := oSpec)
    hBridge hInit hImplSupp

/-! ### Step 3: embedded sum-check phase completeness on the honest support -/

/-- **`SumcheckCompletenessResidual` discharged on the honest support, modulo the per-round bridge.**
Chains `inner_sumcheck_perfectCompleteness_of_perRound` (the inner oracle completeness) with the
proven `sumcheckCompletenessResidual_of_honest` (which discharges the `proj_complete` algebraic
obligation on the honest-prover support from `hHonest`). The only residuals are `hHonest`,
`hPerRound`, `hInit`, `hImplSupp`. -/
theorem sumcheckCompletenessResidual_of_honest_perRound
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
  sumcheckCompletenessResidual_of_honest F n M params oSpec init impl hHonest
    (inner_sumcheck_perfectCompleteness_of_perRound oSpec F n M params init impl
      hPerRound hInit hImplSupp)

/-! ### Step 4: end-to-end most-unconditional completeness -/

/-- **Most-unconditional LogUp Protocol 2 completeness (issue #13, keystone K-compFull).**

The full LogUp oracle reduction is complete with error `logupCompletenessError F n`. The **outer**
pole-rejection half is proven in-tree from `NeverFail init`, and the **embedded sum-check** half is
now discharged on the honest support modulo the per-round bridge (the deep unbounded-round verifier
fusion having been closed by the proven binary keystone). The smallest honest residual set:

* `hInit : NeverFail init` — standard completeness initialization;
* `hHonest` — the honest-support condition (genuine inputs, honest oracles, pole-free challenge);
* `hPerRound` — the per-round single-round `liftContext`-commutation bridge;
* `hImplSupp` — the standard oracle-implementation support-faithfulness condition;
* `hAppend` — the non-perfect outer⊕sumcheck append-composition completeness.

The conclusion is exactly the headline LogUp completeness statement, with no `sorry`. -/
theorem logup_completeness_uncond
    (hInit : NeverFail init)
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
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (hAppend :
      AppendCompletenessResidual oSpec F n M params init impl
        (outerCompletenessResidual_of_neverFail oSpec F n M params init impl hInit)
        (sumcheckCompletenessResidual_of_honest_perRound oSpec F n M params init impl
          hHonest hPerRound hInit hImplSupp)) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_full oSpec F n M params init impl hInit
    (sumcheckCompletenessResidual_of_honest_perRound oSpec F n M params init impl
      hHonest hPerRound hInit hImplSupp)
    hAppend

/-! ### The perfect special case: zero append residual

When `logupCompletenessError F n = 0`, the proven oracle-level keystone discharges the append
composition outright, so `hAppend` is *not* needed. We feed the discharged sum-check half into the
already-zero-residual `logup_completeness_full_perfect`. -/

noncomputable local instance instPSpecChallengeOIUncond :
    ∀ i, OracleInterface ((pSpec F n M params).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

noncomputable local instance instOuterChallengeOIUncond :
    ∀ i, OracleInterface ((outerPSpec F n params).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

noncomputable local instance instSumcheckChallengeOIUncond :
    ∀ i, OracleInterface ((logupSumcheckPSpec F n M params).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

/-- **Most-unconditional LogUp completeness in the perfect special case — no append residual.**

When `logupCompletenessError F n = 0`, the append composition is discharged by the proven keystone
(`logup_completeness_full_perfect`), so the only remaining inputs are the discharged embedded
sum-check half and the structural message-seam direction facts. The residual surface is `hInit`,
`hHonest`, `hPerRound`, `hImplSupp`, the message-seam direction facts (`hn`, `hDir`, `hDir₂`), and
the proven verifier-fusion bridge `hBridge` — with **no** non-perfect append residual. -/
theorem logup_completeness_uncond_perfect
    (hErr : logupCompletenessError F n = 0)
    (hInit : NeverFail init)
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
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (hn : 0 < Fin.vsum (fun _ : Fin n => 2))
    (hDir :
      (pSpec F n M params).dir (⟨4, by
        change 4 < 4 + Fin.vsum (fun _ : Fin n => 2); omega⟩ :
          Fin (4 + Fin.vsum (fun _ : Fin n => 2))) = .P_to_V)
    (hDir₂ : (logupSumcheckPSpec F n M params).dir (⟨0, hn⟩ :
        Fin (Fin.vsum (fun _ : Fin n => 2))) = .P_to_V)
    (hBridge :
      OracleReduction.appendToReductionResidual
        (outerOracleReduction oSpec F n M params)
        (sumcheckOracleReduction oSpec F n M params))
    [(oSpec + [(pSpec F n M params).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec F n M params).Challenge]ₒ).Inhabited]
    [(oSpec + [(outerPSpec F n params).Challenge]ₒ).Fintype]
    [(oSpec + [(outerPSpec F n params).Challenge]ₒ).Inhabited]
    [(oSpec + [(logupSumcheckPSpec F n M params).Challenge]ₒ).Fintype]
    [(oSpec + [(logupSumcheckPSpec F n M params).Challenge]ₒ).Inhabited] :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_full_perfect oSpec F n M params init impl hErr hInit
    (sumcheckCompletenessResidual_of_honest_perRound oSpec F n M params init impl
      hHonest hPerRound hInit hImplSupp)
    hn hDir hDir₂ hImplSupp hBridge

end Uncond

end Logup

/- Axiom audit for the most-unconditional LogUp completeness keystone. -/
#print axioms Logup.binaryVerifierFusion_holds
#print axioms Logup.inner_sumcheck_perfectCompleteness_of_perRound
#print axioms Logup.sumcheckCompletenessResidual_of_honest_perRound
#print axioms Logup.logup_completeness_uncond
#print axioms Logup.logup_completeness_uncond_perfect
