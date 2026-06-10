/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeStateFunction
import ArkLib.OracleReduction.Composition.Sequential.SeamDecompositionRunPartialChallenge

/-!
# Challenge-seam phase-2 experiment body factoring (#114 rbr chain)

`phase2_body_heq_challenge`: the `V_to_P`-seam analogue of `phase2_body_heq` for phase-2 challenge
indices strictly past the seam (`hpos`), via the proven challenge-seam split-prover factoring
`snd_runToRound_natAdd_seam_challenge`. At a challenge seam the positivity of the phase-2 index is a
*hypothesis* (the seam challenge itself, `i₂ = 0`, is handled separately) rather than a consequence
of the seam direction.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

theorem phase2_body_heq_challenge
    (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmtIn : Stmt₁) (witIn : Wit₁) (i₂ : pSpec₂.ChallengeIdx) (hn : 0 < n) (hpos : 0 < ((i₂.1 : Fin n) : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P) :
    HEq
      (do
        let ⟨transcript, _⟩ ←
          prover.runToRound (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn witIn
        let challenge ← OracleComp.liftComp
          ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        pure (transcript, challenge))
      (do
        let ⟨transcript₁, ctxIn₂⟩ ← liftM ((Prover.fst prover).run stmtIn witIn)
        let r ← liftM ((Prover.snd prover).runToRound i₂.1.castSucc ctxIn₂.1 ctxIn₂.2)
        let challenge ← OracleComp.liftComp
          ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        pure (Transcript.appendRight transcript₁ r.1, challenge)) := by
  classical
  have hk0 : 0 < ((i₂.1.castSucc : Fin (n + 1)) : ℕ) := by simpa using hpos
  -- The phase-2 index identity: `(inr i₂).castSucc = ⟨m + (i₂.castSucc).val, _⟩`.
  have hidx : (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by
    ext; simp [ChallengeIdx.inr]
  -- Transcript/state value-type equalities induced by the index identity.
  have hTrTy : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = (pSpec₁ ++ₚ pSpec₂).Transcript
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by rw [hidx]
  have hStTy : prover.PrvState (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = prover.PrvState
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by rw [hidx]
  -- The seam-index transcript/state types, and `prover`'s own state type there (via the merge).
  have hidx2 : (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
      = (Fin.natAdd m i₂.1).castSucc := by ext; simp
  have hStTy' : ((Prover.fst prover).append (Prover.snd prover)).PrvState
      (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
      = prover.PrvState
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by
    rw [hidx2]; exact Prover.merge_PrvState_natAdd_castSucc prover i₂.1 hpos
  have hPrvTy : prover.PrvState (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = ((Prover.fst prover).append (Prover.snd prover)).PrvState
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) :=
    hStTy.trans hStTy'.symm
  -- STEP 1: the bound HEq — appended `runToRound (inr i₂).castSucc` ≍ the seam-factored run (the RHS
  -- of `snd_runToRound_natAdd_seam`), via the index transport.
  have hRunHeq := HEq.trans (Prover.runToRound_heq_index hidx prover stmtIn witIn)
    (Prover.snd_runToRound_natAdd_seam_challenge (P := prover) hn hDir hDir₂ (i₂.1.castSucc) hk0 stmtIn witIn)
  -- The challenge-sampling continuation on the seam-index value type, used as the explicit `f'`.
  let K' : ((pSpec₁ ++ₚ pSpec₂).Transcript
        (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
      × ((Prover.fst prover).append (Prover.snd prover)).PrvState
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)))
      → OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          ((pSpec₁ ++ₚ pSpec₂).Transcript
              (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
            × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) :=
    fun p => do
      let challenge ← OracleComp.liftComp
        ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      pure (p.1, challenge)
  -- STEP 2: bind congruence over the top-level bind into `(seam-run) >>= K'`, then collapse the
  -- inner `do`-block by `bind_assoc` to the stated RHS.  `K'` reads only the transcript component, so
  -- the (discarded) trailing state cast in the seam run is irrelevant.
  refine HEq.trans (Prover.bind_heq_congr (congrArg₂ Prod hTrTy hPrvTy)
    (by rw [hTrTy]) (f' := K') hRunHeq (fun ⟨trA, stA⟩ ⟨trB, stB⟩ hpair => ?_)) (heq_of_eq ?_)
  · -- continuation HEq: same combined `getChallenge`, then `pure (·, challenge)` on HEq transcripts.
    obtain ⟨htr, _⟩ := Prover.prod_heq_split hTrTy hPrvTy hpair
    refine Prover.bind_heq_congr rfl (by rw [hTrTy]) HEq.rfl ?_
    rintro cA cB hc
    exact Prover.pure_heq_pure (by rw [hTrTy]) (Prover.prodMk_heq hTrTy rfl htr hc)
  · -- the inner-block collapse: `(seam-run) >>= K' = stated RHS`.
    show _ >>= K' = _
    simp only [K', bind_assoc, pure_bind]

end Verifier
