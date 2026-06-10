/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeChallengeBody

/-!
# Challenge-seam rbr knowledge-soundness append keystone (`Subsingleton σ`)

The `V_to_P`-seam analogue of `append_rbrKnowledgeSoundness_keystone_subsingleton`. The phase-2
discharge case-splits on the phase-2 challenge index: strictly past the seam (`i₂ > 0`) it mirrors
the message-seam discharge through the challenge-seam body factoring `phase2_body_heq_challenge`
(built on the *syntactic* split-prover seam commutation — `Prover.fst.output` is pure); at the seam
challenge itself (`i₂ = 0`, which exists only at a challenge seam) the per-round flip bound is
isolated as the named residual `hSeamZero`, alongside the (pre-existing, message-seam-shared) inner
reconciliation `hReconcile`. Together with the message keystone and the residual-free empty-seam
keystone (`AppendRbrKnowledgeEmpty.lean`), every seam direction of an appended reduction now has an
rbr knowledge-soundness keystone.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

theorem appendRbrKnowledgeSoundnessPhase2_subsingleton_challenge [Subsingleton σ]
    {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    (hNEW₂ : Nonempty Wit₂) (hInitNF : Pr[⊥ | init] = 0)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (hBound₂ : ∀ stmtIn : Stmt₂, ∀ witIn : Wit₂,
      ∀ prover : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂, ∀ i : pSpec₂.ChallengeIdx,
        Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
          ∃ witMid,
            ¬ kSF₂.toFun i.1.castSucc stmtIn transcript
              (E₂.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
              kSF₂.toFun i.1.succ stmtIn (transcript.concat challenge) witMid
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
                prover.runWithLogToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec₂.getChallenge i) _
              return (transcript, challenge, proveQueryLog))).run' (← init)] ≤
          rbrKnowledgeError₂ i)
    -- The seam-challenge case (`i₂ = 0`, only possible at a `V_to_P` seam): the per-round flip
    -- bound at the seam challenge itself, isolated as a named residual.
    (hSeamZero : ∀ (stmtIn : Stmt₁) (witIn : Wit₁)
      (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (i₂ : pSpec₂.ChallengeIdx),
      ((i₂.1 : Fin n) : ℕ) = 0 →
      Pr[fun ⟨transcript, challenge⟩ =>
          ∃ witMid,
            ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
                (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn transcript
                ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid
                  (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1 stmtIn
                  (transcript.concat challenge) witMid) ∧
              (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
                (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ stmtIn
                (transcript.concat challenge) witMid
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨transcript, _⟩ ←
                prover.runToRound (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn witIn
              let challenge ← OracleComp.liftComp
                ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
                (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              return (transcript, challenge))).run' (← init)] ≤ rbrKnowledgeError₂ i₂)
    (hReconcile : appendRbrKnowledgePhase2SeamReconcile (init := init) (impl := impl)
      V₁ V₂ kSF₁ kSF₂ verify hVerify hInit) :
    appendRbrKnowledgeSoundnessPhase2Residual (init := init) (impl := impl) V₁ V₂
      kSF₁ kSF₂ verify hVerify hInit (rbrKnowledgeError₂ := rbrKnowledgeError₂) := by
  intro stmtIn witIn prover i₂
  classical
  rcases Nat.eq_zero_or_pos ((i₂.1 : Fin n) : ℕ) with hz | hpos
  · exact hSeamZero stmtIn witIn prover i₂ hz
  · -- Abbreviations for the appended phase-2 per-round event `E` and the seam-factored experiment body.
    set E : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
        × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂) → Prop :=
      fun ⟨transcript, challenge⟩ =>
        ∃ witMid,
          ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn transcript
              ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid
                (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1 stmtIn
                (transcript.concat challenge) witMid) ∧
            (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ stmtIn
              (transcript.concat challenge) witMid with hE
    -- The seam index identity and the induced transcript value-type equality.
    have hidx : (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
        = (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by
      ext; simp [ChallengeIdx.inr]
    have hTrTy : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
        = (pSpec₁ ++ₚ pSpec₂).Transcript
            (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by rw [hidx]
    have hResTy : ((pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
          × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
        = ((pSpec₁ ++ₚ pSpec₂).Transcript
              (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
            × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) :=
      congrArg (· × _) hTrTy
    -- STEP 1: transport the appended game to the seam-factored game via `phase2_body_heq`.
    have hbody := phase2_body_heq_challenge prover stmtIn witIn i₂ hn hpos hDir hDir₂
    -- evalDist HEq of the two experiments, from the body HEq.
    have hd : HEq
        (𝒟[init >>= fun s =>
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
            (do
              let ⟨transcript, _⟩ ←
                prover.runToRound (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn witIn
              let challenge ←
                liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) _
              return (transcript, challenge))).run' s])
        (𝒟[init >>= fun s =>
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
            (do
              let ⟨transcript₁, ctxIn₂⟩ ← liftM ((Prover.fst prover).run stmtIn witIn)
              let r ← liftM ((Prover.snd prover).runToRound i₂.1.castSucc ctxIn₂.1 ctxIn₂.2)
              let challenge ←
                liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) _
              return (Transcript.appendRight transcript₁ r.1, challenge))).run' s]) := by
      -- A local `evalDist`-respects-HEq helper.
      have heq_evalDist : ∀ {A B : Type} (hAB : A = B) (a : ProbComp A) (b : ProbComp B),
          HEq a b → HEq (𝒟[a]) (𝒟[b]) := by
        intro A B hAB a b hab; subst hAB; rw [eq_of_heq hab]
      -- A local `(simulateQ _).run'`-respects-HEq helper (for the shared `s`-state).
      have heq_simrun : ∀ {A B : Type} (s : σ) (hAB : A = B)
          (a : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) A)
          (b : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) B), HEq a b →
          HEq ((simulateQ (impl.addLift challengeQueryImpl
                : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) a).run' s)
              ((simulateQ (impl.addLift challengeQueryImpl
                : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) b).run' s) := by
        intro A B s hAB a b hab; subst hAB; rw [eq_of_heq hab]
      refine heq_evalDist hResTy _ _ ?_
      -- The computation-level HEq: shared `init`, HEq continuations (only the value type differs).
      refine Prover.bind_heq_congr rfl hResTy HEq.rfl (fun s s' hs => ?_)
      cases eq_of_heq hs
      exact heq_simrun s hResTy _ _ hbody
    rw [probEvent_congr_heq hResTy _ _ E (fun x => E (hResTy ▸ x)) hd (fun x => Iff.rfl)]
    -- STEP 2: bound the seam-factored game via the Subsingleton bind split.
    -- Under `Subsingleton σ`, `simulateQ_run'_bind_of_subsingleton` distributes the simulated
    -- experiment over the seam bind `liftM (fst.run) >>= REST`.
    simp only [simulateQ_run'_bind_of_subsingleton]
    -- Outer bind over `init`: bound uniformly over each sampled `s`.
    refine probEvent_bind_le_of_forall_le (fun s _hs => ?_)
    -- Inner bind over the (simulated) `fst.run` realization `ctx = (tr₁, seamState, ())`.
    refine probEvent_bind_le_of_forall_le (fun ctx hctx => ?_)
    -- The realized seam statement `s₂ := verify stmtIn tr₁` and the amnesiac re-injection prover that
    -- resumes `Prover.snd prover` from the realized seam state `ctx.2.1`.
    set s₂ : Stmt₂ := verify stmtIn ctx.1 with hs₂
    -- Apply the inner bound `hBound₂` to the amnesiac prover, then `logfree_reduce` to drop its log.
    have hb := hBound₂ s₂ hNEW₂.some (Prover.sndAmnesiac prover ctx.2.1) i₂
    rw [OracleReduction.rbrKnowledge_logfree_reduce impl (Prover.sndAmnesiac prover ctx.2.1) i₂ s₂
        hNEW₂.some init
        (fun x => ∃ witMid, ¬ kSF₂.toFun i₂.1.castSucc s₂ x.1
            (E₂.extractMid i₂.1 s₂ (x.1.concat x.2) witMid) ∧
            kSF₂.toFun i₂.1.succ s₂ (x.1.concat x.2) witMid)] at hb
    -- The amnesiac's partial run is `Prover.snd prover`'s from the seam state `ctx.2.1`.
    simp only [Prover.sndAmnesiac_runToRound] at hb
    -- Under `Subsingleton σ`, the inner `init`-averaged game equals its value at our fixed `s` (all
    -- states are forced equal); with `Pr[⊥|init]=0`, `hb` collapses to the fixed-`s` snd game.
    rw [probEvent_bind_of_const init
        (r := Pr[fun x => ∃ witMid, ¬ kSF₂.toFun i₂.1.castSucc s₂ x.1
              (E₂.extractMid i₂.1 s₂ (x.1.concat x.2) witMid) ∧
              kSF₂.toFun i₂.1.succ s₂ (x.1.concat x.2) witMid
          | (simulateQ (impl.addLift challengeQueryImpl
              : QueryImpl (oSpec + [pSpec₂.Challenge]ₒ) (StateT σ ProbComp))
              (do
                let ⟨transcript, _⟩ ← (Prover.snd prover).runToRound i₂.1.castSucc ctx.2.1 ()
                let challenge ← liftComp (pSpec₂.getChallenge i₂) _
                return (transcript, challenge))).run' s])
        (fun s' _ => by rw [Subsingleton.elim s' s]; rfl),
        hInitNF] at hb
    simp only [tsub_zero, one_mul] at hb
    -- FINAL SEAM RECONCILIATION (the smallest remaining typed residual): the appended phase-2 inner
    -- game (combined challenge oracle, transcript prefixed by the realized phase-1 transcript `ctx.1`,
    -- event read through the composite `KnowledgeStateFunction.append` / `Extractor.RoundByRound.append`)
    -- equals — at our fixed Subsingleton state `s` — the inner `pSpec₂` snd game of `hb` (`pSpec₂`'s own
    -- challenge oracle, `kSF₂`/`E₂` at the realized seam statement `s₂ = verify stmtIn ctx.1`).  Two
    -- ingredients: (a) the right challenge-oracle-seam transfer `evalDist_run'_challengeSeam_right`
    -- (`append_getChallenge_natAdd`), and (b) the gt-event correspondence
    -- `KnowledgeStateFunction.append_toFun_gt` / `appendExtractMid_gt` (the phase-2 analogue of the
    -- proven phase-1 witness-event block), under the `appendRight ctx.1` transcript prefix.
    -- Discharge by the isolated inner seam reconciliation `hReconcile` (the appended combined-oracle
    -- inner game, with the `appendRight ctx.1` prefix and composite gt-event, equals the inner `pSpec₂`
    -- snd game of `hb`).
    unfold appendRbrKnowledgePhase2SeamReconcile at hReconcile
    exact le_of_eq_of_le (hReconcile stmtIn prover i₂ s ctx) hb


/-- **Round-by-round knowledge soundness append keystone, `Subsingleton σ` CHALLENGE-seam case.**
The `V_to_P`-seam analogue of `append_rbrKnowledgeSoundness_keystone_subsingleton`: the phase-2
discharge routes through the challenge-seam body factoring (`phase2_body_heq_challenge`, built on
the syntactic split-prover seam commutation), with the seam-challenge case (`i₂ = 0`, which exists
only at a challenge seam) and the inner seam reconciliation isolated as the two named residuals
`hSeamZero` / `hReconcile`, each quantified over the destructured inner extractors / knowledge
state functions. -/
theorem append_rbrKnowledgeSoundness_keystone_subsingleton_challenge [Subsingleton σ]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE₂ : Nonempty Stmt₂) (hNEW₂ : Nonempty Wit₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂)
    (hSeamZero : ∀ {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
      {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
      {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
      (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
      (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂),
      ∀ (stmtIn : Stmt₁) (witIn : Wit₁)
        (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
        (i₂ : pSpec₂.ChallengeIdx),
        ((i₂.1 : Fin n) : ℕ) = 0 →
        Pr[fun ⟨transcript, challenge⟩ =>
            ∃ witMid,
              ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
                  (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn transcript
                  ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid
                    (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1 stmtIn
                    (transcript.concat challenge) witMid) ∧
                (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
                  (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ stmtIn
                  (transcript.concat challenge) witMid
          | do
            (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
              (do
                let ⟨transcript, _⟩ ←
                  prover.runToRound (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn witIn
                let challenge ← OracleComp.liftComp
                  ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
                  (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                return (transcript, challenge))).run' (← init)] ≤ rbrKnowledgeError₂ i₂)
    (hReconcile : ∀ {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
      {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
      {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
      (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
      (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂),
      appendRbrKnowledgePhase2SeamReconcile (init := init) (impl := impl) V₁ V₂ kSF₁ kSF₂
        verify hVerify hInit) :
      (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  obtain ⟨WitMid₁, E₁, kSF₁, hBound₁⟩ := h₁
  obtain ⟨WitMid₂, E₂, kSF₂, hBound₂⟩ := h₂
  exact ⟨_, Extractor.RoundByRound.append E₁ E₂ verify,
    KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit,
    appendRbrKnowledgeSoundnessPerRound V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hNE₂ hNEW₂
      hBound₁ (appendRbrKnowledgeSoundnessPhase2_subsingleton_challenge V₁ V₂ kSF₁ kSF₂ verify
        hVerify hInit hNEW₂ hInitNF hn hDir hDir₂ hBound₂ (hSeamZero kSF₁ kSF₂)
        (hReconcile kSF₁ kSF₂))⟩

end Verifier
