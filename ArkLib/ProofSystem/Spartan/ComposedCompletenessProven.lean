/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.ComposedCompleteness
import ArkLib.ProofSystem.Spartan.ComposedCompletenessLeaves
import ArkLib.ProofSystem.Spartan.FirstChallengeComplete
import ArkLib.ProofSystem.Spartan.LinearCombinationComplete

/-!
# #114 — Spartan composed-completeness: remaining leaves + full assembly (worktree verification).

Verifies, at the exact endpoints pinned by
`Spartan.Spec.Bricks.composedCompletenessResidual_of_five_leaves` (ComposedCompleteness.lean):

(a) the `finalCheck` leaf (`h₈`): perfect completeness of the terminal 0-round `CheckClaim`
    phase from `secondSumcheckRelOutBF` into `finalCheckRelOut` (definitionally `Set.univ`);
(b) the honest-target leaf (`h₆`): the D1 design gap. Machine-checked characterization of the
    mismatch (the legacy `prependTarget` adapter emits the hardwired target `0`, and a target-`0`
    statement lies in `secondSumcheckRelInBF` only if the honest RLC value vanishes), plus the
    fix: the honest RLC-target adapter `prependRLCTarget` is perfectly complete into
    `secondSumcheckRelInBF` from `prependRLCTargetRelIn`, and the linearCombination pushforward
    of the sendEvalClaim output relation refines `prependRLCTargetRelIn` (honesty threading);
(c) the assembly: `composedCompletenessResidual_proven_114c` — the official
    `composedCompletenessResidual` for `composedPIOP_Rc`, with NO leaf hypotheses left; only the
    standard honest-implementation side conditions (`NeverFail init`, support-faithfulness,
    state-preservation, no-failure of `impl`) remain.

NOTE: `PhaseCompletenessLeaves` is NOT imported: it redeclares `Spartan.Spec.sendEvalClaimRelOut`
and `Spartan.Spec.linearCombinationRelOut` (also declared by `ComposedCompletenessLeaves`), so the
two modules cannot be imported together (duplicate-declaration clash). Its only unique content
(`firstMessage_perfectCompleteness`) is not needed: the consumer discharges the `firstMessage`
leaf internally via `SendSingleWitness.oracleReduction_completeness`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Spartan.Spec.Bricks

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] [VCVCompatible R] (pp : PublicParams)
  {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-! ## (a) The `finalCheck` leaf (`h₈`), at the consumer's exact endpoints -/

/-- **`finalCheck` leaf of `composedCompletenessResidual_of_five_leaves` (`h₈`)**: perfect
completeness of the terminal 0-round `CheckClaim` phase from `secondSumcheckRelOutBF` into
`finalCheckRelOut` (definitionally `Set.univ`). Instance of the in-tree
`Bricks2.finalCheck_perfectCompleteness` (0-round deterministic run; the predicate's queries are
simulated honestly and its result is discarded, so the only content is totality and
prover/verifier statement agreement). -/
theorem finalCheck_perfectCompleteness_leaf_114c :
    (finalCheck R pp oSpec).perfectCompleteness init impl
      (secondSumcheckRelOutBF (R := R) pp) (finalCheckRelOut R pp) :=
  Bricks2.finalCheck_perfectCompleteness pp oSpec (secondSumcheckRelOutBF (R := R) pp)

/-! ## (b) The honest-target leaf (`h₆`): D1 mismatch characterization + the fix -/

/-- **D1 mismatch, machine-checked (i): the legacy `prependTarget` adapter emits the hardwired
target `0`.** Its deterministic 0-round run is a single `pure` prepending `(0 : R)` — instance of
`prependSlot_run`. -/
theorem prependTarget_run_target_zero_114c
    (stmt : Statement.AfterLinearCombination R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i) :
    (prependTarget (R := R) pp oSpec).toReduction.run (stmt, oStmt) () =
      (pure (((default : (!p[] : ProtocolSpec 0).FullTranscript),
          (((0 : R), stmt), oStmt), ()), (((0 : R), stmt), oStmt)) :
        OptionT (OracleComp _) _) :=
  prependSlot_run R oSpec _ _ stmt oStmt

/-- **D1 mismatch, machine-checked (ii): a target-`0` statement satisfies `secondSumcheckRelInBF`
only if the honest RLC value vanishes.** Hence the legacy `prependTarget` (which always emits
target `0`, by (i)) cannot be perfectly complete into `secondSumcheckRelInBF` from any input
relation containing an instance with nonzero honest RLC — the honest-target adapter
`prependRLCTarget` is required. -/
theorem prependTarget_target_zero_forces_rlc_zero_114c
    (stmt : Statement.AfterLinearCombination R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i)
    (h : ((((0 : R), stmt), oStmt), ()) ∈ secondSumcheckRelInBF (R := R) pp) :
    (0 : R) = ∑ idx, stmt.1 idx *
      evalClaimValue R pp stmt.2 (fun i => oStmt (.inr i)) idx :=
  h.2

/-- **Honesty-threading inclusion (the D1 fix, relation side):** the linear-combination
pushforward of the `sendEvalClaim` output relation (over the bridge-free first-sum-check output)
refines the honest RLC-target input relation: the R1CS conjunct transports verbatim, and the
function-level eval-claim honesty specializes pointwise. -/
theorem linearCombinationRelOutOf_subset_prependRLCTargetRelIn_114c :
    linearCombinationRelOutOf (R := R) pp
        (sendEvalClaimRelOut R pp (firstSumcheckRelOutBF (R := R) pp))
      ⊆ prependRLCTargetRelIn (R := R) pp := by
  rintro x ⟨h1, h2⟩
  exact ⟨h1, fun idx => congrFun h2 idx⟩

/-- **The honest-target leaf (`h₆`), at the consumer's exact endpoints**: the honest RLC-target
adapter is perfectly complete from the honesty-carrying relation chain endpoint
`linearCombinationRelOutOf (sendEvalClaimRelOut firstSumcheckRelOutBF)` into
`secondSumcheckRelInBF`. -/
theorem prependRLCTarget_perfectCompleteness_leaf_114c :
    (prependRLCTarget (R := R) pp oSpec).perfectCompleteness init impl
      (linearCombinationRelOutOf (R := R) pp
        (sendEvalClaimRelOut R pp (firstSumcheckRelOutBF (R := R) pp)))
      (secondSumcheckRelInBF (R := R) pp) := by
  have h := prependRLCTarget_perfectCompleteness_secondSumcheckRelInBF (R := R) pp oSpec
    (σ := σ) (init := init) (impl := impl)
  unfold OracleReduction.perfectCompleteness Reduction.perfectCompleteness at h ⊢
  exact Reduction.completeness_relIn_mono init impl
    (linearCombinationRelOutOf_subset_prependRLCTargetRelIn_114c pp) h

/-! ## Remaining leaves at the consumer's endpoints -/

/-- The `firstChallenge` leaf (`h₂`) at the consumer's endpoints: `firstMessageRelOut` and
`firstSumcheckRelInBF` are definitionally the honest `firstChallengeRelIn`/`firstChallengeRelOut`
endpoints of the unconditional `firstChallenge_perfectCompleteness`. -/
theorem firstChallenge_perfectCompleteness_leaf_114c :
    (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl
      (firstMessageRelOut (R := R) pp) (firstSumcheckRelInBF (R := R) pp) := by
  have h := firstChallenge_perfectCompleteness (R := R) (pp := pp) (oSpec := oSpec)
    (σ := σ) (init := init) (impl := impl)
  unfold OracleReduction.perfectCompleteness Reduction.perfectCompleteness at h ⊢
  exact Reduction.completeness_relIn_mono init impl (fun _ hx => hx) h

/-! ## (c) The full assembly: all five leaves discharged -/

/-- **Composed Spartan PIOP perfect completeness, fully discharged (issue #114).**
`composedCompletenessResidual` for `composedPIOP_Rc` holds with **no leaf hypotheses**: all
eight phase perfect-completenesses are in-tree machine-checked theorems, threaded along the
honesty-carrying relation chain

`spartanRelIn → firstMessageRelOut → firstSumcheckRelInBF → firstSumcheckRelOutBF →
 sendEvalClaimRelOut … → linearCombinationRelOutOf … → secondSumcheckRelInBF →
 secondSumcheckRelOutBF → finalCheckRelOut`.

Only the standard honest-implementation side conditions remain as inputs. -/
theorem composedCompletenessResidual_proven_114c
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    composedCompletenessResidual R pp oSpec (composedPIOP_Rc pp oSpec) init impl := by
  -- h₄: parametric sendEvalClaim leaf at the bridge-free first-sum-check output
  have h₄ := sendEvalClaim_perfectCompleteness R pp oSpec init impl
    (firstSumcheckRelOutBF (R := R) pp)
  -- h₅: parametric linearCombination leaf at the honesty-carrying relation
  have h₅ := linearCombination_perfectCompleteness_of (R := R) (pp := pp) (oSpec := oSpec)
    (init := init) (impl := impl)
    (sendEvalClaimRelOut R pp (firstSumcheckRelOutBF (R := R) pp))
  exact composedCompletenessResidual_of_five_leaves pp oSpec hm hn
    (firstChallenge_perfectCompleteness_leaf_114c pp oSpec)
    h₄ h₅
    (prependRLCTarget_perfectCompleteness_leaf_114c pp oSpec)
    (finalCheck_perfectCompleteness_leaf_114c pp oSpec)
    hInit hImplSupp himplSP himplNF

end Spartan.Spec.Bricks

-- Axiom audit: every leaf + the assembly must be sorry-free
-- ([propext, Classical.choice, Quot.sound] only).
#print axioms Spartan.Spec.Bricks.finalCheck_perfectCompleteness_leaf_114c
#print axioms Spartan.Spec.Bricks.prependTarget_run_target_zero_114c
#print axioms Spartan.Spec.Bricks.prependTarget_target_zero_forces_rlc_zero_114c
#print axioms Spartan.Spec.Bricks.linearCombinationRelOutOf_subset_prependRLCTargetRelIn_114c
#print axioms Spartan.Spec.Bricks.prependRLCTarget_perfectCompleteness_leaf_114c
#print axioms Spartan.Spec.Bricks.firstChallenge_perfectCompleteness_leaf_114c
#print axioms Spartan.Spec.Bricks.composedCompletenessResidual_proven_114c
-- Imported leaves the assembly rests on:
#print axioms Spartan.Spec.sendEvalClaim_perfectCompleteness
#print axioms Spartan.Spec.linearCombination_perfectCompleteness_of
#print axioms Spartan.Spec.firstChallenge_perfectCompleteness
#print axioms Spartan.Spec.Bricks.prependRLCTarget_perfectCompleteness_secondSumcheckRelInBF
#print axioms Bricks2.finalCheck_perfectCompleteness
#print axioms Spartan.Spec.Bricks.composedCompletenessResidual_of_five_leaves
