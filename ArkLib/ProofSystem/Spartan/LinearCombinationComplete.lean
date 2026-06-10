/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Spartan.Composition

/-!
# `linearCombination` phase perfect completeness, parametric in the input relation (#114)

`ComposedCompletenessLeaves.linearCombination_perfectCompleteness` proves the Spartan RLC
challenge phase perfectly complete for the *pinned* R1CS pass-through relations
(`linearCombinationRelIn` → `linearCombinationRelOut`). The composed-PC fold
(`composedCompletenessResidual_of_five_leaves`, `ComposedCompleteness.lean`) however pins the
phase's **input** relation to whatever the upstream `sendEvalClaim` leaf emits —
`sendEvalClaimRelOut … (firstSumcheckRelOutBF …)`, which carries the bundled eval-claim *honesty*
conjunct that the pinned relations drop (and which the downstream honest RLC-target adapter
`prependRLCTarget` needs).

Since `linearCombination` is a pure V→P challenge round — statement and oracles pass through
unchanged, the sampled challenge is merely recorded — it is perfectly complete from **any** input
relation `rel` to the challenge-stripped pushforward `linearCombinationRelOutOf rel`. This module
proves exactly that:

* `linearCombinationRelOutOf` — the pushforward output relation (strip the recorded challenge,
  require the underlying pair in `rel`);
* `linearCombination_perfectCompleteness_of` — the parametric leaf perfect completeness. The
  five-leaves consumer's `h₅` is the instance `rel := relE` for whatever `relE` the `sendEvalClaim`
  leaf provides, with `relF := linearCombinationRelOutOf relE`.
-/

open MvPolynomial OracleComp OracleSpec OracleQuery OracleInterface ProtocolSpec

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
/-- The `linearCombination` phase records the sampled RLC challenge and passes statement and
oracles through unchanged, so its honest output relation from an arbitrary input relation `rel` is
the challenge-stripped pushforward: drop the recorded challenge `x.1.1.1` and require the
underlying (statement, oracles, witness) tuple to lie in `rel`. -/
def linearCombinationRelOutOf
    (rel : Set ((Statement.AfterSendEvalClaim R pp ×
        (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit)) :
    Set ((Statement.AfterLinearCombination R pp ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  { x | ((x.1.1.2, x.1.2), ()) ∈ rel }

/-- `VerifierOnly` instance for the `linearCombination` protocol shape. Kept `local`: the exported
instance lives in `ComposedCompletenessLeaves` (`instLinearCombinationVerifierOnly`), which this
module deliberately does not import. -/
local instance :
    VerifierOnly (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1) where
  verifier_first' := by simp

set_option linter.unusedSimpArgs false in
omit [DecidableEq R] [SampleableType R] in
/-- **The `linearCombination` phase is perfectly complete from any input relation** to its
challenge-stripped pushforward `linearCombinationRelOutOf rel`: the phase samples the RLC
challenge, records it, and passes statement/oracles/witness through unchanged. This is the
parametric form of the leaf hypothesis `h₅` of `composedCompletenessResidual_of_five_leaves`
(instantiate `rel` with the output relation of the `sendEvalClaim` leaf). -/
theorem linearCombination_perfectCompleteness_of
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : Set ((Statement.AfterSendEvalClaim R pp ×
        (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit)) :
    (oracleReduction.linearCombination R pp oSpec).perfectCompleteness init impl
      rel (linearCombinationRelOutOf (R := R) pp rel) := by
  simp only [OracleReduction.perfectCompleteness, oracleReduction.linearCombination,
    linearCombinationRelOutOf]
  simp only [Reduction.perfectCompleteness_eq_prob_one]
  intro ⟨stmt, oStmt⟩ wit hRelIn
  simp only [OracleReduction.toReduction, Reduction.run,
    Prover.run_of_verifier_first, linearCombinationProver, linearCombinationVerifier,
    OracleVerifier.toVerifier, Verifier.run]
  simp_rw [show (pure : _ → OptionT (OracleComp _) _) = fun x => (pure (some x) :
    OracleComp _ _) from rfl]
  simp only [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
    pure_bind, bind_assoc]
  erw [simulateQ_bind]
  erw [simulateQ_bind]
  simp only [QueryImpl.addLift_def, simulateQ_pure,
    QueryImpl.simulateQ_add_liftComp_right, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_query,
    ← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
    pure_bind, bind_assoc, map_pure, monadLift_pure, monadLift_bind]
  erw [simulateQ_bind]
  simp only [QueryImpl.addLift_def, simulateQ_pure,
    QueryImpl.simulateQ_add_liftComp_right, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_query,
    ← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
    pure_bind, bind_assoc, map_pure, monadLift_pure, monadLift_bind,
    OptionT.run_mk, OptionT.run_pure, OptionT.run_bind, OptionT.run,
    Option.getM, Option.bind_some, Option.elimM,
    FullTranscript.challenges, FullTranscript.messages, ChallengeIdx, Challenge]
  erw [simulateQ_query]
  simp only [Fin.isValue, Fin.vcons_of_one, ChallengeIdx,
    Challenge, ofPFunctor_toPFunctor, QueryImpl.liftTarget_self, MessageIdx,
    Message, bind_map_left, StateT.run'_eq, StateT.run_bind, map_bind, OptionT.mk_bind,
    Set.mem_setOf_eq, probEvent_eq_one_iff, probFailure_bind_eq_zero_iff,
    OptionT.probFailure_liftM, HasEvalPMF.probFailure_eq_zero, OptionT.support_liftM,
    Prod.forall, true_and, support_bind, Set.mem_iUnion, OptionT.mem_support_iff,
    OptionT.run_mk, support_map, Set.mem_image, Prod.exists, exists_and_right,
    exists_eq_right, exists_prop, forall_exists_index, and_imp, Prod.mk.injEq]
  constructor <;> intro <;> intro <;> intro <;> intro
  all_goals try erw [simulateQ_bind]
  all_goals simp only [MonadLift.monadLift, liftM, monadLift, MonadLiftT.monadLift]
  all_goals simp only [OracleComp.liftComp_pure, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_pure, simulateQ_id', pure_bind, bind_assoc, map_pure, monadLift_pure,
    OptionT.run_mk, OptionT.run_pure, OptionT.run_bind, OptionT.run,
    StateT.run'_eq, probFailure_eq_zero,
    support_pure, Set.mem_singleton_iff, Prod.eq_iff_fst_eq_snd_eq]
  all_goals try erw [simulateQ_pure]
  all_goals try simp_all only [simulateQ_pure, pure_bind, map_pure,
    OptionT.run_mk, OptionT.run_pure, OptionT.run_bind, OptionT.run,
    StateT.run'_eq, StateT.run_pure, probFailure_eq_zero,
    support_pure, support_map, Set.mem_singleton_iff, Set.mem_image,
    OptionT.probFailure_eq, probOutput_pure]
  · erw [simulateQ_bind, simulateQ_pure]
    simp only [pure_bind]
    erw [simulateQ_pure]
    simp [map_pure, OptionT.mk, probFailure_pure]
  · intro trFull lc fsc fc x1 oOut wOut lc2 fsc2 fc2 x2 oOut2 sI hsI rng
    erw [simulateQ_bind] at rng
    simp only [liftComp_eq_liftM, pure_bind, simulateQ_pure, OptionT.lift,
      OptionT.run_mk, map_pure] at rng
    erw [simulateQ_pure] at rng
    simp only [pure_bind, simulateQ_pure, support_pure, StateT.run, StateT.run',
      Set.mem_singleton_iff, Prod.mk.injEq] at rng
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := rng
    refine ⟨?_, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    · simpa only [Set.mem_setOf_eq] using hRelIn
    · funext i
      rcases i with j | j <;> rfl

end Spartan.Spec

-- Axiom check
#print axioms Spartan.Spec.linearCombination_perfectCompleteness_of
