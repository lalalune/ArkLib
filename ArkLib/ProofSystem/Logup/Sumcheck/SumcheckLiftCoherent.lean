/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckBridge
import ArkLib.OracleReduction.LiftContext.Coherence

/-!
# Honest oracle-simulation bricks for the LogUp embedded-sumcheck lift coherence (issue #13)

Transferring the generic `Sumcheck.Spec` completeness / RBR-soundness through the LogUp embedded
sumcheck `liftContext` requires the framework coherence obligation
`OracleVerifier.LiftContextCoherent` (design note #433). Its only non-trivial component is the
per-query **faithfulness** condition `hfaith`: under the honest *outer* LogUp oracles, the lens'
virtual-oracle reconstruction `logupSumcheckOracleLens.simOStmt` must agree with the honest *inner*
`Q`-oracle answer.

`simOStmt ⟨(), r⟩` queries the outer multiplicity / table / column / helper oracles at the point `r`,
assembles their evaluations into `PointEvaluations`, and returns `qAtPoint … r …` — which equals the
honest `Q`-polynomial evaluation `eval r Q` by `logupSumcheckPolynomial_finalEval` (the assembled
evaluations satisfy `logupPointEvaluationsAgree` by construction, since each honest oracle answer
*is* the corresponding `lagrangeOracleEval`).

This file proves the **atomic oracle-simulation bricks** underlying that reduction — the hard,
reusable core, mirroring the Spartan first/second-sumcheck faithfulness developments
(`FirstSumcheckFaithful` / `SecondSumcheckFaithful`):

* `simulateQ_simOracle_subspec_query` / `simulateQ_simOracle_liftComp_query`: simulating a single
  honest outer-oracle query (in either the `HasQuery` monad-lift form or the `SubSpec`/`liftComp`
  coercion form the lens emits) under the single-family honest oracle returns the genuine point
  evaluation `answer (oos idx) r`. Proven via `simulateQ_spec_query`.
* `list_mapM_pure`: a `mapM` of a pointwise-`pure` function collapses to a `pure` of the mapped list
  (used for the column / helper `mapM` reconstructions).

All are axiom-clean. Assembling them into the full `simOStmt` faithfulness (and thence the
`LiftContextCoherent` instance) is the remaining engineering step: the per-query bricks reduce the
multiplicity and table queries directly; the column / helper `mapM`s additionally need the
`mapM`-internal queries normalised to the same form the bricks match (the lens emits those under the
`SubSpec` coercion inside a `List.mapM` binder, where `simp` does not fire the brick), then closed
with `logupSumcheckPolynomial_finalEval`.
-/

open OracleComp OracleSpec OracleInterface OracleVerifier.LiftContext

namespace Logup

section LiftCoherent

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)] [SampleableType F]
variable (n M : ℕ) (params : ProtocolParams M)

/-- **Atomic single-query reduction (`HasQuery` form).** Simulating one honest outer-oracle query
(lifted from the family sub-spec via the `HasQuery` monad lift) under the single-family honest oracle
returns the genuine point evaluation. -/
@[simp] theorem simulateQ_simOracle_subspec_query
    (oos : ∀ i, OStmtAfterOuter F n M params i)
    (qi : [OStmtAfterOuter F n M params]ₒ.Domain) :
    simulateQ (simOracle oSpec oos)
        (query (spec := [OStmtAfterOuter F n M params]ₒ) qi :
          OracleComp (oSpec + [OStmtAfterOuter F n M params]ₒ) _)
      = pure (OracleInterface.answer (oos qi.1) qi.2) := by
  erw [simulateQ_spec_query]
  rfl

/-- **Atomic single-query reduction (`SubSpec`/`liftComp` coercion form).** The same fact for the
query shape the lens emits inside a `List.mapM` (the explicit `OracleComp (oSpec + …)` annotation
routes through the sub-spec coercion `liftComp`). -/
@[simp] theorem simulateQ_simOracle_liftComp_query
    (oos : ∀ i, OStmtAfterOuter F n M params i)
    (q : OracleQuery [OStmtAfterOuter F n M params]ₒ F) :
    simulateQ (simOracle oSpec oos)
        (OracleComp.liftComp (q : OracleComp [OStmtAfterOuter F n M params]ₒ F)
          (oSpec + [OStmtAfterOuter F n M params]ₒ))
      = pure (q.cont (OracleInterface.answer (oos q.input.1) q.input.2)) := by
  rw [OracleComp.liftComp_query]
  change (q.cont <$>
    simulateQ (simOracle oSpec oos)
      (liftM ((oSpec + [OStmtAfterOuter F n M params]ₒ).query (Sum.inr q.input)))) = _
  erw [simulateQ_spec_query]
  rfl

/-- `mapM` of a pointwise-`pure` function over a list collapses to a `pure` of the mapped list. -/
@[simp] theorem list_mapM_pure {α β : Type} (f : α → β) (l : List α) :
    (l.mapM (fun a => (pure (f a) : OracleComp oSpec β)) : OracleComp oSpec (List β))
      = pure (l.map f) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

end LiftCoherent

end Logup

#print axioms Logup.simulateQ_simOracle_subspec_query
#print axioms Logup.simulateQ_simOracle_liftComp_query
#print axioms Logup.list_mapM_pure
