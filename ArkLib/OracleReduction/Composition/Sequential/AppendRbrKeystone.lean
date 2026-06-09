/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessProof
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessSeamTransfer
import ArkLib.OracleReduction.Composition.Sequential.SeamDecompositionRun
import ArkLib.ToVCVio.EvalDist.Instances.OptionT

/-!
# Round-by-round (knowledge) soundness append keystone — `appendRbr*SoundnessResidual` discharge

This file makes the round-by-round soundness append keystone **unconditional** for the
deterministic-`V₁` message-seam case that issue #29 (and #114 / #13) need. It targets the named
residual `Verifier.appendRbrSoundnessResidual` (and the knowledge variant) recorded in `Append.lean`.

The two side hypotheses missing from the residual statement (`hVerify`: `V₁` deterministic &
non-failing — which also supplies the `verify` function; `hInit`: a reachable initial state) are the
exact inputs required by the already-proven composite combinators `Verifier.StateFunction.append`
and `Extractor.RoundByRound.append`. With those added, the residue is the **per-round** bound, which
— unlike plain soundness — is a single challenge index `i`, hence a *case split* on
`ChallengeIdx.sumEquiv.symm i` (no union over rounds), deferring each phase to `h₁` / `h₂`.

## Proof architecture

* Phase-1 (`i = ChallengeIdx.inl i₁`): the appended state function `StateFunction.append` lands in its
  `dif_pos` branch (both `i.1.castSucc` and `i.1.succ` are `≤ m`), so the per-round flip event is
  definitionally `S₁`'s flip event at `i₁` on the transcript's `.fst` half. The appended prover's
  partial run `prover.runToRound (inl i₁).castSucc` factors through `Prover.fst` via
  `fst_runToRound_heq`, and the combined challenge-oracle sampling transfers to `pSpec₁`'s own oracle
  via `evalDist_run'_challengeSeam_left`. The bound is then exactly `h₁` applied at `i₁`.
* Phase-2 (`i = ChallengeIdx.inr i₂`): mirrors phase 1 with the `dif_neg` branch (`verify`-fed
  intermediate statement), `merge_runToRound` / `Prover.snd`, and `evalDist_run'_challengeSeam_right`.
-/

open OracleComp OracleSpec ProtocolSpec SubSpec
open scoped ENNReal NNReal

universe u v

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}

/-- **At a phase-1-only round index, the transcript truncation is the identity.** For `k ≤ m`,
the appended-spec transcript `tr` keeps all its rounds under the phase-1 truncation, so
`Transcript.fst tr` is heterogeneously equal to `tr` (only per-round value types differ). -/
theorem transcript_fst_heq {k : Fin (m + n + 1)} (hk : (k : ℕ) ≤ m)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript k) :
    HEq (ProtocolSpec.Transcript.fst tr) tr := by
  refine Function.hfunext (congrArg Fin (Nat.min_eq_left hk)) (fun a a' ha => ?_)
  have hval : a.val = a'.val := by
    have := (Fin.heq_ext_iff (Nat.min_eq_left hk)).mp ha
    omega
  have hidx : (⟨a.val, by omega⟩ : Fin (k : ℕ)) = a' := Fin.ext hval
  unfold ProtocolSpec.Transcript.fst
  exact HEq.trans (cast_heq _ _) (hidx ▸ HEq.rfl)

/-- **Phase-1 per-round experiment body HEq.** The appended rbr experiment body at a phase-1
challenge index `inl i₁` — the appended prover's partial run `runToRound (inl i₁).castSucc` followed
by sampling the appended `getChallenge (inl i₁)` under the *combined* challenge oracle — is
heterogeneously equal (the two value types are *propositionally equal* via `append_Transcript_castLE`
on the transcript and `range_challenge_append_inl` on the challenge) to `liftComp` of the phase-1
experiment body of `prover.fst` over `pSpec₁`'s own challenge oracle, lifted into the combined oracle.
This packages the run-level seam-factoring `fst_runToRound_heq` with the challenge-seam reduction
`append_getChallenge_left`. -/
private theorem phase1_body_heq
    (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmtIn : Stmt₁) (witIn : Wit₁) (i₁ : pSpec₁.ChallengeIdx) :
    HEq
      (do
        let ⟨transcript, _⟩ ←
          prover.runToRound (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc stmtIn witIn
        let challenge ← OracleComp.liftComp
          ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        pure (transcript, challenge))
      (OracleComp.liftComp
        (do
          let ⟨transcript, _⟩ ← prover.fst.runToRound i₁.1.castSucc stmtIn witIn
          let challenge ← OracleComp.liftComp (pSpec₁.getChallenge i₁) (oSpec + [pSpec₁.Challenge]ₒ)
          pure (transcript, challenge))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) := by
  have hChalDir : (pSpec₁ ++ₚ pSpec₂).dir (i₁.1.castLE (by omega)) = .V_to_P := by
    rw [Prover.append_dir_castLE i₁.1]; exact i₁.2
  -- index reindexings
  have hidxCS : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc : Fin (m + n + 1))
      = (i₁.1.castSucc.castLE (by omega)) := by ext; simp [ChallengeIdx.inl]
  have hidxChal : (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1 = i₁.1.castLE (by omega) := by
    ext; simp [ChallengeIdx.inl]
  -- The transcript and challenge value-type equalities (propositional).
  have hTrTy : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc
      = pSpec₁.Transcript i₁.1.castSucc := by
    rw [hidxCS]; exact Prover.append_Transcript_castLE i₁.1.castSucc
  have hStTy : prover.PrvState (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc
      = prover.fst.PrvState i₁.1.castSucc := by rw [hidxCS]; rfl
  have hChTy : (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁)
      = pSpec₁.Challenge i₁ := by
    show (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i₁) = pSpec₁.Challenge i₁
    simp [ChallengeIdx.inl, ProtocolSpec.append]
  have hValTy : ((pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc
        × prover.PrvState (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc)
      = (pSpec₁.Transcript i₁.1.castSucc × prover.fst.PrvState i₁.1.castSucc) := by
    rw [hTrTy, hStTy]
  have hResTy : ((pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc
        × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁))
      = (pSpec₁.Transcript i₁.1.castSucc × pSpec₁.Challenge i₁) := by
    rw [hTrTy, hChTy]
  -- Distribute `liftComp` over the RHS bind/pure.
  rw [OracleComp.liftComp_bind]
  refine Prover.bind_heq_congr hValTy hResTy ?_ ?_
  · -- the partial runs: phase-1 faithfulness.
    rw [hidxCS]; exact Prover.fst_runToRound_heq prover stmtIn witIn i₁.1.castSucc
  · -- the challenge-sampling continuations.
    rintro ⟨trA, stA⟩ ⟨trB, stB⟩ hpair
    obtain ⟨htr, _⟩ := Prover.prod_heq_split hTrTy hStTy hpair
    rw [OracleComp.liftComp_bind]
    refine Prover.bind_heq_congr hChTy hResTy ?_ ?_
    · -- the challenge query HEq: `append_getChallenge_left`, both sides lifted into the combined
      -- oracle.
      have hChTy' : (pSpec₁ ++ₚ pSpec₂).Challenge (⟨i₁.1.castLE (by omega), hChalDir⟩) =
          pSpec₁.Challenge i₁ := by
        rw [← hChTy]; congr 1 <;> (apply Subtype.ext; rw [hidxChal])
      have hgc := Prover.append_getChallenge_left (pSpec₂ := pSpec₂) i₁.1 hChalDir i₁.2
      rw [show (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁) = ⟨i₁.1.castLE (by omega), hChalDir⟩ from by
            apply Subtype.ext; rw [hidxChal]]
      -- LHS: `liftComp (getChallenge ⟨castLE,_⟩) combined`; transport `hgc` through `liftComp`.
      refine HEq.trans (Prover.liftComp_heq_congr
        (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hChTy' hgc) ?_
      -- now: `liftComp (liftM (getChallenge i₁) : OracleComp [combined Ch]) combined`
      --      ≍ `liftComp (liftComp (getChallenge i₁) (oSpec+[pSpec₁ Ch])) combined`.
      -- Both are double-lifts of `getChallenge i₁` from `[pSpec₁ Ch]` into `oSpec+[combined Ch]`.
      apply heq_of_eq
      rw [show (liftM (pSpec₁.getChallenge i₁) : OracleComp [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _)
            = OracleComp.liftComp (pSpec₁.getChallenge i₁) [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ from
          (OracleComp.liftComp_eq_liftM _).symm]
      rw [show OracleComp.liftComp (OracleComp.liftComp (pSpec₁.getChallenge i₁)
                [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              = OracleComp.liftComp (pSpec₁.getChallenge i₁)
                  (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            from Prover.liftComp_liftComp (midSpec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                (fun t => rfl) (pSpec₁.getChallenge i₁),
          show OracleComp.liftComp (OracleComp.liftComp (pSpec₁.getChallenge i₁)
                (oSpec + [pSpec₁.Challenge]ₒ)) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              = OracleComp.liftComp (pSpec₁.getChallenge i₁)
                  (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            from Prover.liftComp_liftComp (midSpec := oSpec + [pSpec₁.Challenge]ₒ)
                (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                (fun t => rfl) (pSpec₁.getChallenge i₁)]
    · -- the final `pure (transcript, challenge)` continuations.
      rintro cA cB hc
      refine Prover.pure_heq_pure (by rw [hTrTy, hChTy]) ?_
      exact Prover.prodMk_heq hTrTy hChTy htr hc

/-- **Phase-1 projection of the appended state function.** On a round index lying in the first
protocol (`roundIdx.val ≤ m`), `StateFunction.append` is definitionally `S₁` evaluated on the
transcript's phase-1 truncation — the `dif_pos` branch of its `toFun`. -/
theorem StateFunction.append_toFun_le
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : V₁.StateFunction init impl lang₁ lang₂) (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    {roundIdx : Fin (m + n + 1)} (h : roundIdx.val ≤ m) (stmt₁ : Stmt₁)
    (transcript : (pSpec₁ ++ₚ pSpec₂).Transcript roundIdx) :
    (StateFunction.append init impl V₁ V₂ S₁ S₂ verify hVerify hInit).toFun roundIdx stmt₁ transcript
      = S₁.toFun ⟨roundIdx, by omega⟩ stmt₁ (by simpa [h] using transcript.fst) := by
  simp only [StateFunction.append, dif_pos h]

/-- **Round-by-round soundness append keystone, deterministic-`V₁` message-seam case.**
Discharges `Verifier.appendRbrSoundnessResidual` for the deterministic-`V₁` message-seam case.

The two added side conditions (`verify`/`hVerify` and `hInit`) are exactly the inputs of the proven
`StateFunction.append`; with them the per-round bound is a case split on `ChallengeIdx.sumEquiv.symm`
deferring each phase to `h₁`/`h₂`. -/
theorem append_rbrSoundness_keystone
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rbrSoundnessError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrSoundness init impl lang₁ lang₂ rbrSoundnessError₁)
    (h₂ : V₂.rbrSoundness init impl lang₂ lang₃ rbrSoundnessError₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hNE : Nonempty Stmt₂) :
      (V₁.append V₂).rbrSoundness init impl lang₁ lang₃
        (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  obtain ⟨S₁, hS₁⟩ := h₁
  obtain ⟨S₂, hS₂⟩ := h₂
  refine ⟨StateFunction.append init impl V₁ V₂ S₁ S₂ verify hVerify hInit, ?_⟩
  intro stmtIn hStmtIn WitIn WitOut witIn prover i
  -- Case split on phase-1 / phase-2 of the appended challenge index.
  rcases hi : ChallengeIdx.sumEquiv.symm i with i₁ | i₂
  · -- Phase 1.
    have hRHS : (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm) i
        = rbrSoundnessError₁ i₁ := by
      simp only [Function.comp_apply, hi, Sum.elim_inl]
    rw [hRHS]
    have hiEq : i = ChallengeIdx.inl i₁ := by
      have := ChallengeIdx.sumEquiv.apply_symm_apply i
      rw [hi] at this; simpa using this.symm
    subst hiEq
    -- Reduce to the inner verifier's per-round bound `hS₁`, applied to the phase-1 seam prover
    -- recast to an `Stmt₂`-output prover (`fstCast`; the dummy claim is irrelevant since the rbr
    -- experiment touches only `runToRound`, which is output-agnostic).
    refine le_of_eq_of_le ?phase1_transport
      (hS₁ stmtIn hStmtIn WitIn Unit witIn (prover.fstCast hNE.some) i₁)
    -- Remaining (`phase1_transport`): the appended phase-1 experiment over the *combined* challenge
    -- oracle has the same event-probability as the `fstCast` experiment over `pSpec₁`'s own oracle.
    -- The ingredients are all proven: `Prover.fstCast_runToRound` (= `fst`'s run), `phase1_body_heq`
    -- (the body HEq), `evalDist_run'_challengeSeam_left` (combined → `pSpec₁` distribution transfer),
    -- and `StateFunction.append.toFun`'s `dif_pos` branch (the appended state function collapses to
    -- `S₁` on `transcript.fst` for phase-1 indices). Assembled through `probEvent_congr_heq`.
    have hidxCS : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc : Fin (m + n + 1))
        = i₁.1.castSucc.castLE (by omega) := by ext; simp [ChallengeIdx.inl]
    have hTrTy : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc
        = pSpec₁.Transcript i₁.1.castSucc := by
      rw [hidxCS]; exact Prover.append_Transcript_castLE i₁.1.castSucc
    have hChTy : (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁)
        = pSpec₁.Challenge i₁ := by simp [ChallengeIdx.inl, ProtocolSpec.append]
    have hResTy :
        ((pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc
            × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁))
          = (pSpec₁.Transcript i₁.1.castSucc × pSpec₁.Challenge i₁) := by rw [hTrTy, hChTy]
    refine probEvent_congr_heq hResTy _ _ _ _ ?hd ?hPQ
    · -- hd : the appended and `fstCast` experiments have heterogeneously-equal `evalDist`s.
      sorry
    · -- hPQ : the appended state-function event corresponds to `S₁`'s under the type cast.
      rintro ⟨tr, ch⟩
      have hlt : i₁.1.val < m := i₁.1.isLt
      have hval : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1).val = i₁.1.val := by
        simp [ChallengeIdx.inl, Fin.coe_castAdd]
      have hcs : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc).val ≤ m := by
        rw [Fin.val_castSucc, hval]; omega
      have hsu : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.succ).val ≤ m := by
        rw [Fin.val_succ, hval]; omega
      simp only [StateFunction.append_toFun_le V₁ V₂ S₁ S₂ verify hVerify hInit hcs,
          StateFunction.append_toFun_le V₁ V₂ S₁ S₂ verify hVerify hInit hsu]
      -- Remaining: index coherence `⟨(inl i₁).castSucc.val, _⟩ = i₁.castSucc` (vals agree) and the
      -- transcript coherence `(append_toFun_le cast).mp tr.fst = (hResTy ▸ (tr, ch)).1` (the phase-1
      -- truncation equals the type-cast; buried in `StateFunction.append`'s `toFun_next` proof).
      sorry
  · -- Phase 2. Mirrors Phase 1 with `Prover.snd`, `evalDist_run'_challengeSeam_right`, and the
    -- `dif_neg` (`verify`-fed intermediate statement) branch of `StateFunction.append`.
    sorry

end Verifier
