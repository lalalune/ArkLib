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

-- STATEMENT REPAIR (2026-06-04): restricted to state-preserving impl; literal form is false for
-- stateful impl, counterexample in FRONTIER NOTE.
--
-- The literal `rbrSoundness_implies_soundness` is FALSE for an arbitrary *stateful* `impl`: a
-- malicious prover that queries the shared oracle `oSpec` (routed through `impl`) advances the shared
-- `σ`-state so the verifier runs from a state OUTSIDE `support init`, whereas `StateFunction.toFun_full`
-- only forbids acceptance from a fresh `init` sample.  Concrete counterexample (documented in
-- Execution.lean's FRONTIER NOTE / commit a755799d): `σ = Bool`, `init = pure false`, an `impl` whose
-- prover-query flips the state to a verifier-accepting value while `sf (last n)` is identically false
-- — rbr-sound with error 0, yet unsound.  The implication is TRUE in the standard cryptographic
-- setting where the prover-side simulation preserves `support init` (subsingleton `σ` / stateless /
-- distribution-preserving challenge-only `impl`).  We capture that as the hypothesis
-- `Reduction.StatePreserving` (Execution.lean), the minimal honest restriction the proof consumes
-- (only to discharge obligation (A)'s `s' ∈ support init`).
/-- Round-by-round soundness with error `rbrSoundnessError` implies soundness with error
`∑ i, rbrSoundnessError i`, where the sum is over all rounds `i`, **for a state-preserving `impl`**
(the literal statement is false for an arbitrary stateful `impl`; see the STATEMENT REPAIR note). -/
theorem rbrSoundness_implies_soundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0)
    (hPres : ∀ {WitIn WitOut : Type}
      (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec),
      Reduction.StatePreserving (Reduction.mk prover verifier) init impl) :
      rbrSoundness init impl langIn langOut verifier rbrSoundnessError →
        soundness init impl langIn langOut verifier (∑ i, rbrSoundnessError i) := by
  -- PROOF (probability bridge, ArkLib#1), under the state-preserving-impl STATEMENT REPAIR.
  --
  -- 1. Destructure the rbr hypothesis to get the state function `sf` and the per-round bound `hsf`.
  -- 2. `intro` the soundness game's prover/statement; reduce to
  --      `Pr[verifierOut ∈ langOut | full game] ≤ ∑ i, rbrSoundnessError i`.
  -- 3. `probEvent_le_sum_of_imp_exists` over `κ = pSpec.ChallengeIdx` splits into:
  --      (A) the support-implication `himp` (accept ⇒ ∃ challenge-round flip), and
  --      (B) the per-round bound `Pr[flip_i | full game] ≤ rbrSoundnessError i`.
  -- (A) is discharged by `exists_challenge_flip_of_full` + the contrapositive of `toFun_full`,
  --     with the `s' ∈ support init` obligation closed by the state-preserving hypothesis
  --     (`mem_support_verdict_init_of_statePreserving`).
  -- (B) chains the soundness game's flip probability to the rbr game's via the failure-monotone
  --     keystone transport (`runToRound_eq_bind_continueFromTo` +
  --     `probEvent_simulateQ_run'_bind_trailing_le` + `fst_map_runToRound_succ_challenge`).
  intro hRbr
  obtain ⟨sf, hsf⟩ := hRbr
  simp only [soundness]
  intro WitIn' WitOut' witIn' prover stmtIn hStmtIn
  -- Abbreviations matching the soundness game.
  set reduction := Reduction.mk prover verifier with hred
  set pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
    impl.addLift challengeQueryImpl with hpImpl
  -- The soundness game, as an `OptionT ProbComp` computation.
  set game : OptionT ProbComp ((FullTranscript pSpec × StmtOut × WitOut') × StmtOut) :=
    OptionT.mk (do (simulateQ pImpl (reduction.run stmtIn witIn').run).run' (← init)) with hgame
  -- The per-round flip predicate (depends only on the realized transcript prefix).
  set P : pSpec.ChallengeIdx → ((FullTranscript pSpec × StmtOut × WitOut') × StmtOut) → Prop :=
    fun i x =>
      ¬ sf.toFun i.1.castSucc stmtIn (x.1.1.take i.1.castSucc.val i.1.castSucc.is_le) ∧
        sf.toFun i.1.succ stmtIn
          (Transcript.concat (x.1.1 i.1) (x.1.1.take i.1.castSucc.val i.1.castSucc.is_le))
    with hP
  -- Step 3: union bound via implication.
  refine le_trans
    (Verifier.StateFunction.probEvent_le_sum_of_imp_exists game
      (fun x => x.2 ∈ langOut) P ?_) ?_
  · -- Obligation (A): on the support, accept ⇒ ∃ challenge-round flip.
    intro x hx hAccept
    -- Unfold the game support to extract a fresh `init` sample `s` and a game support point.
    rw [hgame, OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, mem_support_bind_iff] at hx
    obtain ⟨s, hs, hx⟩ := hx
    -- The verdict is reachable from a fresh `init` sample (state preservation discharges `s'∈support`).
    have hverdict := Reduction.mem_support_verdict_init_of_statePreserving
      reduction init impl (hPres prover) stmtIn witIn' s hs x hx
    -- Contrapositive of `toFun_full`: if `¬ sf (last) …` then `x.2 ∉ langOut`. So `sf (last) …`.
    have hlast : sf.toFun (Fin.last n) stmtIn
        (x.1.1.take (Fin.last n).val (Fin.last n).is_le) := by
      by_contra hnot
      have hzero := sf.toFun_full stmtIn (x.1.1.take (Fin.last n).val (Fin.last n).is_le) hnot
      rw [probEvent_eq_zero_iff] at hzero
      exact hzero x.2 hverdict hAccept
    -- First-crossing on the realized transcript lands on a challenge round.
    obtain ⟨i, hcast, hsucc⟩ :=
      Verifier.StateFunction.exists_challenge_flip_of_full init impl sf stmtIn hStmtIn x.1.1 hlast
    exact ⟨i, hcast, hsucc⟩
  · -- Obligation (B): the per-round bound, summed over challenge rounds.
    rw [ENNReal.coe_finset_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    -- For each challenge round `i`, bound the soundness-game flip probability by `rbrSoundnessError i`.
    have hi := hsf stmtIn hStmtIn WitIn' WitOut' witIn' prover i
    classical
    refine le_trans ?_ hi
    -- (B.1) Characterize the `OptionT` flip event as a *success-conjunction* on the underlying run:
    -- the flip must hold on a genuine (non-failing) verifier accept (failure does not count).
    rw [hgame, Verifier.StateFunction.probEvent_optionT_mk_eq_elim, OptionT.run_mk]
    -- (B.2) Both games thread `init` identically; reduce to a per-state `ProbComp` bound.
    refine Verifier.StateFunction.probEvent_bind_mono_heteroEvent (fun s hs => ?_)
    -- Per-state goal (fixed `s ∈ support init`): soundness-game flip prob ≤ rbr-game flip prob,
    -- discharged by the failure-monotone keystone transport.
    exact Reduction.probEvent_run_run'_flip_le_rbr sf i stmtIn prover s

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
