/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.StateRestoration
import ArkLib.OracleReduction.Salt

/-!
# Implications between security notions

This file collects the implications between the various security notions.

For now, we only state the theorems. It's likely that we will split this file into multiple files in
a single `Implication` folder in the future, each file for the proof of a single implication.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace Verifier

section Implications

/- TODO: add the following results
- `knowledgeSoundness` implies `soundness`
- `roundByRoundSoundness` implies `soundness`
- `roundByRoundKnowledgeSoundness` implies `roundByRoundSoundness`
- `roundByRoundKnowledgeSoundness` implies `knowledgeSoundness`

In other words, we have a lattice of security notions, with `knowledge` and `roundByRound` being
two strengthenings of soundness.
-/

/-- Knowledge soundness with knowledge error `knowledgeError < 1` implies soundness with the same
soundness error `knowledgeError`, and for the corresponding input and output languages. -/
theorem knowledgeSoundness_implies_soundness
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (knowledgeError : ℝ≥0) (hLt : knowledgeError < 1) :
      knowledgeSoundness init impl relIn relOut verifier knowledgeError →
        soundness init impl relIn.language relOut.language verifier knowledgeError := by
  simp [knowledgeSoundness, soundness, Set.language]
  intro extractor hKS WitIn' WitOut' witIn' prover stmtIn hStmtIn
  sorry
  -- have hKS' := hKS stmtIn witIn' prover
  -- clear hKS
  -- contrapose! hKS'
  -- constructor
  -- · convert hKS'; rename_i result
  --   obtain ⟨transcript, queryLog, stmtOut, witOut⟩ := result
  --   simp
  --   placeholder
  -- · simp only [Set.language, Set.mem_setOf_eq, not_exists] at hStmtIn
  --   simp only [Functor.map, Seq.seq, PMF.bind_bind, Function.comp_apply, PMF.pure_bind, hStmtIn,
  --     PMF.bind_const, PMF.pure_apply, eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte,
  --     zero_add, ℝ≥0.coe_lt_one_iff, hLt]

/-- Round-by-round soundness with error `rbrSoundnessError` implies soundness with error
`∑ i, rbrSoundnessError i`, where the sum is over all rounds `i`. -/
theorem rbrSoundness_implies_soundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) :
      rbrSoundness init impl langIn langOut verifier rbrSoundnessError →
        soundness init impl langIn langOut verifier (∑ i, rbrSoundnessError i) := by
  -- PROOF SPINE (probability bridge, ArkLib#1). The combinatorial + union-bound + first-crossing
  -- backbone is fully banked and assembled below; the single remaining gap is the per-round
  -- distributional marginal (see FRONTIER below and the FRONTIER NOTE in Execution.lean).
  --
  -- 1. Destructure the rbr hypothesis to get the state function `sf` and the per-round bound `hsf`.
  -- 2. `intro` the soundness game's prover/statement; reduce the goal to
  --      `Pr[verifierOut ∈ langOut | full game] ≤ ∑ i, rbrSoundnessError i`.
  -- 3. `Verifier.StateFunction.probEvent_le_sum_of_imp_exists` reduces (2) to: on the support, the
  --    accept event implies `∃ i : ChallengeIdx, flip_i` (a per-round flip on the realized
  --    transcript prefix), PLUS the per-round bound `Pr[flip_i | full game] ≤ rbrSoundnessError i`.
  -- 4. The support-implication is `Verifier.StateFunction.exists_challenge_flip_of_full` applied to
  --    each accepting support point: `toFun_full` (contrapositive, via `probEvent_pos`) gives
  --    `sf (last n) stmtIn (tr.take)` for the realized full transcript `tr`, and `stmtIn ∉ langIn`
  --    gives `¬ sf 0`, so the first-crossing lands on a challenge round.
  -- 5. The per-round bound chains: `Pr[flip_i | full game] ≤ Pr[flip_i | rbr game i] ≤
  --    rbrSoundnessError i = hsf i`, where the first `≤` is the failure-monotone marginal.
  --
  -- FRONTIER (the only missing connective): the first `≤` in step 5. The flip event depends only on
  -- the round-`i.succ` transcript prefix; in the full game that prefix is produced by
  -- `runToRound (last n)` followed by the trailing `receiveChallenge`/`sendMessage`/`output` and
  -- verifier steps, whereas the rbr game produces it via `runToRound i.castSucc >>= getChallenge`.
  --
  -- BANKED bridge ingredients (all proven, committed):
  --   • `Verifier.StateFunction.probEvent_bind_trailing_le` — failure-monotone trailing bind;
  --   • `Verifier.StateFunction.probEvent_simulateQ_run'_bind_trailing_le` — the STATE-AWARE
  --     transport of that across `simulateQ so · |>.run' s` for an *arbitrary* stateful `so`
  --     (this was the previously-identified hard probabilistic frontier — now closed);
  --   • `Prover.fst_map_runToRound_succ_challenge` — per-round prover factorization;
  --   • `Prover.fin_take_snoc_of_le` — geometric prefix preservation under `snoc`;
  --   • `exists_challenge_flip_of_full`, `probEvent_le_sum_of_imp_exists` — combinatorial backbone.
  --
  -- REMAINING (structural assembly only): a `runToRound` *round-range decomposition*
  --   `runToRound (last n) = runToRound i.succ >>= continueRoundsFrom`  (a plain `OracleComp`
  -- equality, since the continuation only `processRound`s further rounds), so that
  -- `probEvent_simulateQ_run'_bind_trailing_le` can drop the `continueRoundsFrom` tail and the
  -- `Reduction.run` verifier/output tail, exposing the `runToRound i.succ` prefix to which
  -- `fst_map_runToRound_succ_challenge` then applies, landing on the rbr game `hsf i`.  This
  -- decomposition is a dependent-`Fin`-range induction (the continuation's type depends on `i`);
  -- it is the last keystone.  See Execution.lean FRONTIER NOTE.
  sorry

/-- Round-by-round knowledge soundness with error `rbrKnowledgeError` implies round-by-round
soundness with the same error `rbrKnowledgeError`. -/
theorem rbrKnowledgeSoundness_implies_rbrSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (h : verifier.rbrKnowledgeSoundness init impl relIn relOut rbrKnowledgeError) :
    verifier.rbrSoundness init impl relIn.language relOut.language rbrKnowledgeError := by
  unfold rbrSoundness
  unfold rbrKnowledgeSoundness at h
  obtain ⟨WitMid, extractor, kSF, h⟩ := h
  refine ⟨kSF.toStateFunction, ?_⟩
  intro stmtIn hRelIn WitIn' WitOut' witIn' prover chalIdx
  simp_all
  sorry

/-- Round-by-round knowledge soundness with error `rbrKnowledgeError` implies knowledge soundness
with error `∑ i, rbrKnowledgeError i`, where the sum is over all rounds `i`. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) :
      rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError →
        knowledgeSoundness init impl relIn relOut verifier (∑ i, rbrKnowledgeError i) := by sorry

-- /-- Round-by-round soundness for a protocol implies state-restoration soundness for the same
-- protocol with arbitrary added non-empty salts. -/
-- theorem rbrSoundness_implies_srSoundness_addSalt
--     {init : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id)}
--     {impl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp)}
--     (langIn : Set StmtIn) (langOut : Set StmtOut)
--     (verifier : Verifier oSpec StmtIn StmtOut pSpec)
--     (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0)
--     (Salt : pSpec.MessageIdx → Type) [∀ i, Nonempty (Salt i)] [∀ i, Fintype (Salt i)] :
--       rbrSoundness init impl langIn langOut verifier rbrSoundnessError →
--         Verifier.StateRestoration.soundness init impl langIn langOut (verifier.addSalt Salt)
--           (∑ i, (rbrSoundnessError i)) := by placeholder

-- /-- Round-by-round knowledge soundness for a protocol implies state-restoration
-- knowledge soundness for the same protocol with arbitrary added non-empty salts. -/
-- theorem rbrKnowledgeSoundness_implies_srKnowledgeSoundness_addSalt
--     {init : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id)}
--     {impl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp)}
--     (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
--     (verifier : Verifier oSpec StmtIn StmtOut pSpec)
--     (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0)
--     (Salt : pSpec.MessageIdx → Type) [∀ i, Nonempty (Salt i)] [∀ i, Fintype (Salt i)] :
--       rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError →
--         Verifier.StateRestoration.knowledgeSoundness init impl relIn relOut
--           (verifier.addSalt Salt) (∑ i, rbrKnowledgeError i) := by placeholder

-- STATEMENT REPAIR (2026-06-04): DELETED `srSoundness_addSalt_implies_srSoundness_original` and
-- `srKnowledgeSoundness_addSalt_implies_srKnowledgeSoundness_original`.
--
-- Both theorems were provably misconceived (and had literal `sorry` placeholders inside their own
-- *statements*, for the original game's `init`/`impl`, so they could not even be coherently stated).
-- They asserted that state-restoration (knowledge) soundness of the *salted* protocol implies
-- state-restoration (knowledge) soundness of the *original* protocol. But:
--
--   1. There is no principled way to source the original SR game's `(init, impl)` over
--      `srChallengeOracle StmtIn pSpec` from the salted game's `(srInit, srImpl)` over
--      `srChallengeOracle StmtIn (pSpec.addSalt Salt)` — the salted SR challenge oracle ranges over
--      strictly more transcripts. The two `sorry`s in the conclusion stood exactly where that
--      (nonexistent) derivation was required.
--
--   2. State-restoration soundness is precisely the soundness notion that is **NOT preserved** under
--      salting: ArkLib/OracleReduction/Salt.lean (L198-205) records an explicit in-repo
--      counterexample — "the verifier sends one random bit per round, and accepts iff it sends zero
--      for every round" — for which SR (knowledge) soundness fails to transfer across `addSalt`.
--
-- See docs/kb/audits/gh-issues-campaign-2026-06-04.md ("Design gaps", salt counterexample item) and
-- the (commented-out, deliberately deferred) `rbrSoundness_implies_srSoundness_addSalt` family above,
-- which captures the only salt/SR relationship that is conjectured to hold (rbr ⇒ SR under salt).

/-- State-restoration soundness implies basic (straightline) soundness.

This theorem shows that state-restoration security is a strengthening of basic soundness.
The error is preserved in the implication. -/
theorem srSoundness_implies_soundness
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))
    (srSoundnessError : ℝ≥0) :
      Verifier.StateRestoration.soundness srInit srImpl langIn langOut verifier srSoundnessError →
        soundness init impl langIn langOut verifier srSoundnessError := by
  sorry

/-- State-restoration knowledge soundness implies basic (straightline) knowledge soundness.

This theorem shows that state-restoration knowledge soundness is a strengthening of basic
knowledge soundness. The error is preserved in the implication. -/
theorem srKnowledgeSoundness_implies_knowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))
    (srKnowledgeError : ℝ≥0) :
      Verifier.StateRestoration.knowledgeSoundness srInit srImpl relIn relOut
        verifier srKnowledgeError →
      knowledgeSoundness init impl relIn relOut verifier srKnowledgeError := by sorry

-- TODO: state that round-by-round security implies state-restoration security for protocol with
-- arbitrary added (non-empty?) salts

-- TODO: state that state-restoration security for added salts imply state-restoration security for
-- the original protocol (with some better parameters)

-- TODO: state that state-restoration security implies basic security

end Implications

end Verifier
