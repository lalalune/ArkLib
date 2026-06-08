/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.SeamDecomposition

/-!
# Phase-1 run faithfulness for the seam decomposition (issue #13)

Companion to `SeamDecomposition.lean`.  Proves that the phase-1 restriction `Prover.fst P` of an
arbitrary (malicious) prover `P` over `pSpec₁ ++ₚ pSpec₂` faithfully reproduces `P`'s own run over
the first `m` rounds:

`fst_runToRound_heq : HEq (P.runToRound (castLE j) stmt wit) (liftM ((Prover.fst P).runToRound j stmt wit))`

This is the left half of the run-level seam decomposition `P.run = (fst P).run >>= (snd P).run`
needed to discharge `appendSoundnessResidual`.  The proof mirrors `append_runToRound_left` but, since
`(fst P).PrvState ≡ P.PrvState ∘ castLE` *definitionally*, the prover-state HEqs collapse to `rfl`
(the helper `fst_PrvState_castSucc'/_succ'` provide the residual Fin-index `congrArg`s).  All
declarations are axiom-clean and `sorry`-free.

Supporting per-round faithfulness: `fst_sendMessage_left`, `fst_receiveChallenge_left`,
`fst_processRound_left_{message,challenge}`; generic helper `map_heq_self`.
-/

open OracleComp ProtocolSpec OracleVerifier.Append

universe u

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₃ Wit₃ : Type} {m n : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

namespace Prover

theorem map_heq_self {α β : Type} {κ : Type} {spec : OracleSpec κ} (hαβ : α = β)
    (g : α → β) (X : OracleComp spec α) (hg : ∀ a, HEq (g a) a) : HEq (g <$> X) X := by
  subst hαβ
  rw [show g = id from funext fun a => eq_of_heq (hg a), id_map]

/-- **Left-round `sendMessage` faithfulness for `fst`.** `P`'s sendMessage at a left round equals
(heterogeneously) `fst P`'s own sendMessage; the defining cast/transport map is HEq-trivial. -/
theorem fst_sendMessage_left (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (i : Fin m)
    (hDir' : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castLE (show m ≤ m + n by omega) i) = .P_to_V)
    (hDir : pSpec₁.dir i = .P_to_V)
    (state : P.PrvState (Fin.castLE (show m ≤ m + n by omega) i).castSucc) :
    HEq (P.sendMessage ⟨Fin.castLE (show m ≤ m + n by omega) i, hDir'⟩ state)
        ((Prover.fst P).sendMessage ⟨i, hDir⟩
          (cast (congrArg P.PrvState
                  (show ((Fin.castLE (show m ≤ m + n by omega) i).castSucc)
                     = Fin.castLE (show m + 1 ≤ m + n + 1 by omega) i.castSucc from by ext; simp))
                state)) := by
  dsimp only [Prover.fst]
  refine (HEq.trans (map_heq_self ?_ _ _ ?_)
    (sendMessage_heq_congr rfl (cast_heq _ _))).symm
  · rw [append_Message_castLE i hDir' hDir]; congr 1
  · rintro ⟨msg, st⟩
    exact prodMk_heq (append_Message_castLE i hDir' hDir).symm rfl (cast_heq _ _) HEq.rfl

/-- **Left-round `receiveChallenge` faithfulness for `fst`** (function-valued analogue of
`fst_sendMessage_left`). -/
theorem fst_receiveChallenge_left (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (i : Fin m)
    (hDir' : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castLE (show m ≤ m + n by omega) i) = .V_to_P)
    (hDir : pSpec₁.dir i = .V_to_P)
    (state : P.PrvState (Fin.castLE (show m ≤ m + n by omega) i).castSucc) :
    HEq (P.receiveChallenge ⟨Fin.castLE (show m ≤ m + n by omega) i, hDir'⟩ state)
        ((Prover.fst P).receiveChallenge ⟨i, hDir⟩
          (cast (congrArg P.PrvState
                  (show ((Fin.castLE (show m ≤ m + n by omega) i).castSucc)
                     = Fin.castLE (show m + 1 ≤ m + n + 1 by omega) i.castSucc from by ext; simp))
                state)) := by
  have hChal : (pSpec₁ ++ₚ pSpec₂).Challenge ⟨Fin.castLE (show m ≤ m + n by omega) i, hDir'⟩
      = pSpec₁.Challenge ⟨i, hDir⟩ := by
    change Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (Fin.castLE (show m ≤ m + n by omega) i)
      = pSpec₁.«Type» i
    rw [Fin.vappend_eq_append,
      show (Fin.castLE (show m ≤ m + n by omega) i) = Fin.castAdd n i from by ext; simp,
      Fin.append_left]
  dsimp only [Prover.fst]
  refine (HEq.trans (map_heq_self ?_ _ _ ?_)
    (receiveChallenge_heq_congr rfl (cast_heq _ _))).symm
  · rw [hChal]; congr 1
  · intro f
    refine Function.hfunext hChal.symm ?_
    intro c c' hcc
    have hc : cast hChal.symm c = c' := eq_of_heq ((cast_heq _ _).trans hcc)
    rw [hc]

theorem fst_PrvState_castSucc' (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (i : Fin m) :
    P.PrvState (Fin.castLE (show m ≤ m + n by omega) i).castSucc
      = (Prover.fst P).PrvState i.castSucc :=
  congrArg P.PrvState (by ext; simp)

theorem fst_PrvState_succ' (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (i : Fin m) :
    P.PrvState (Fin.castLE (show m ≤ m + n by omega) i).succ = (Prover.fst P).PrvState i.succ :=
  congrArg P.PrvState (by ext; simp)

/-- **Left-round `processRound` faithfulness (message branch).** -/
theorem fst_processRound_left_message (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (i : Fin m) (hDir₁ : pSpec₁.dir i = .P_to_V)
    (curA : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.castLE (show m ≤ m + n by omega) i).castSucc
        × P.PrvState (Fin.castLE (show m ≤ m + n by omega) i).castSucc))
    (cur₁ : OracleComp (oSpec + [pSpec₁.Challenge]ₒ)
      (pSpec₁.Transcript i.castSucc × (Prover.fst P).PrvState i.castSucc))
    (hcur : HEq curA (liftM cur₁ :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) :
    HEq (P.processRound (Fin.castLE (show m ≤ m + n by omega) i) curA)
      (liftM ((Prover.fst P).processRound i cur₁) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
  have hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castLE (show m ≤ m + n by omega) i) = .P_to_V := by
    rw [append_dir_castLE]; exact hDir₁
  rw [processRound_message P (Fin.castLE (show m ≤ m + n by omega) i) hDir curA,
    processRound_message (Prover.fst P) i hDir₁ cur₁]
  simp only [liftM_bind, liftM_pure]
  refine bind_heq_congr
    (by rw [append_Transcript_castSucc i, fst_PrvState_castSucc' P i])
    (by rw [append_Transcript_succ i, fst_PrvState_succ' P i]) hcur ?_
  rintro ⟨t, s⟩ ⟨t', s'⟩ hr
  obtain ⟨ht, hs⟩ := prod_heq_split (append_Transcript_castSucc i) (fst_PrvState_castSucc' P i) hr
  dsimp only
  have hcollapse : (liftM (liftM ((Prover.fst P).sendMessage ⟨i, hDir₁⟩ s') :
        OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
      = liftM ((Prover.fst P).sendMessage ⟨i, hDir₁⟩ s' : OracleComp oSpec _) := rfl
  rw [hcollapse]
  apply bind_heq_congr (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
    (β := (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.castLE (show m ≤ m + n by omega) i).succ
      × P.PrvState (Fin.castLE (show m ≤ m + n by omega) i).succ)
    (β' := pSpec₁.Transcript i.succ × (Prover.fst P).PrvState i.succ)
    (α := (pSpec₁ ++ₚ pSpec₂).Message ⟨Fin.castLE (show m ≤ m + n by omega) i, hDir⟩
      × P.PrvState (Fin.castLE (show m ≤ m + n by omega) i).succ)
    (α' := pSpec₁.Message ⟨i, hDir₁⟩ × (Prover.fst P).PrvState i.succ)
    (by rw [append_Message_castLE i hDir hDir₁, fst_PrvState_succ' P i])
    (by rw [append_Transcript_succ i, fst_PrvState_succ' P i])
  · -- sendMessage HEq (lifted)
    have hαeq : ((pSpec₁ ++ₚ pSpec₂).Message ⟨Fin.castLE (show m ≤ m + n by omega) i, hDir⟩
          × P.PrvState (Fin.castLE (show m ≤ m + n by omega) i).succ)
        = (pSpec₁.Message ⟨i, hDir₁⟩ × (Prover.fst P).PrvState i.succ) := by
      rw [append_Message_castLE i hDir hDir₁, fst_PrvState_succ' P i]
    have hbase : HEq (P.sendMessage ⟨Fin.castLE (show m ≤ m + n by omega) i, hDir⟩ s)
        ((Prover.fst P).sendMessage ⟨i, hDir₁⟩ s') :=
      (fst_sendMessage_left P i hDir hDir₁ s).trans
        (sendMessage_heq_congr rfl ((cast_heq _ _).trans hs))
    change HEq (OracleComp.liftComp (P.sendMessage ⟨Fin.castLE (show m ≤ m + n by omega) i, hDir⟩ s)
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
        (OracleComp.liftComp
          (OracleComp.liftComp ((Prover.fst P).sendMessage ⟨i, hDir₁⟩ s')
            (oSpec + [pSpec₁.Challenge]ₒ))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
    rw [liftComp_liftComp (spec := oSpec) (midSpec := oSpec + [pSpec₁.Challenge]ₒ)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)
      ((Prover.fst P).sendMessage ⟨i, hDir₁⟩ s')]
    exact liftComp_heq_congr (spec := oSpec)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hαeq hbase
  · rintro ⟨msg, ns⟩ ⟨msg', ns'⟩ hmsg
    refine pure_heq_pure (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (by rw [append_Transcript_succ i, fst_PrvState_succ' P i]) ?_
    obtain ⟨hm, hns⟩ :=
      prod_heq_split (append_Message_castLE i hDir hDir₁) (fst_PrvState_succ' P i) hmsg
    refine prodMk_heq (append_Transcript_succ i) (fst_PrvState_succ' P i) ?_ hns
    exact concat_heq i ht hm

/-- **Left-round `processRound` faithfulness (challenge branch).** -/
theorem fst_processRound_left_challenge (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (i : Fin m) (hDir₁ : pSpec₁.dir i = .V_to_P)
    (curA : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.castLE (show m ≤ m + n by omega) i).castSucc
        × P.PrvState (Fin.castLE (show m ≤ m + n by omega) i).castSucc))
    (cur₁ : OracleComp (oSpec + [pSpec₁.Challenge]ₒ)
      (pSpec₁.Transcript i.castSucc × (Prover.fst P).PrvState i.castSucc))
    (hcur : HEq curA (liftM cur₁ :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) :
    HEq (P.processRound (Fin.castLE (show m ≤ m + n by omega) i) curA)
      (liftM ((Prover.fst P).processRound i cur₁) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
  have hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castLE (show m ≤ m + n by omega) i) = .V_to_P := by
    rw [append_dir_castLE]; exact hDir₁
  rw [processRound_challenge' P (Fin.castLE (show m ≤ m + n by omega) i) hDir curA,
    processRound_challenge' (Prover.fst P) i hDir₁ cur₁]
  simp only [liftM_bind, liftM_pure]
  refine bind_heq_congr
    (by rw [append_Transcript_castSucc i, fst_PrvState_castSucc' P i])
    (by rw [append_Transcript_succ i, fst_PrvState_succ' P i]) hcur ?_
  rintro ⟨t, s⟩ ⟨t', s'⟩ hr
  obtain ⟨ht, hs⟩ := prod_heq_split (append_Transcript_castSucc i) (fst_PrvState_castSucc' P i) hr
  dsimp only
  have hChalEq : (pSpec₁ ++ₚ pSpec₂).Challenge ⟨Fin.castLE (show m ≤ m + n by omega) i, hDir⟩
      = pSpec₁.Challenge ⟨i, hDir₁⟩ := by
    change Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (Fin.castLE (show m ≤ m + n by omega) i)
      = pSpec₁.«Type» i
    rw [Fin.vappend_eq_append,
      show (Fin.castLE (show m ≤ m + n by omega) i) = Fin.castAdd n i from by ext; simp,
      Fin.append_left]
  refine bind_heq_congr (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
    hChalEq
    (by rw [append_Transcript_succ i, fst_PrvState_succ' P i]) ?_ ?_
  · exact liftM_heq_congr (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hChalEq
      (append_getChallenge_left i hDir hDir₁)
  · rintro chalA chal₁ hchal
    have hcollapse : (liftM (liftM ((Prover.fst P).receiveChallenge ⟨i, hDir₁⟩ s') :
          OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
        = liftM ((Prover.fst P).receiveChallenge ⟨i, hDir₁⟩ s' : OracleComp oSpec _) := by rfl
    rw [hcollapse]
    have hrecvBase : HEq (P.receiveChallenge ⟨Fin.castLE (show m ≤ m + n by omega) i, hDir⟩ s)
        ((Prover.fst P).receiveChallenge ⟨i, hDir₁⟩ s') :=
      (fst_receiveChallenge_left P i hDir hDir₁ s).trans
        (receiveChallenge_heq_congr rfl ((cast_heq _ _).trans hs))
    refine bind_heq_congr (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (α := (pSpec₁ ++ₚ pSpec₂).Challenge ⟨Fin.castLE (show m ≤ m + n by omega) i, hDir⟩
        → P.PrvState (Fin.castLE (show m ≤ m + n by omega) i).succ)
      (α' := pSpec₁.Challenge ⟨i, hDir₁⟩ → (Prover.fst P).PrvState i.succ)
      (β := (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.castLE (show m ≤ m + n by omega) i).succ
        × P.PrvState (Fin.castLE (show m ≤ m + n by omega) i).succ)
      (β' := pSpec₁.Transcript i.succ × (Prover.fst P).PrvState i.succ)
      (by rw [hChalEq, fst_PrvState_succ' P i])
      (by rw [append_Transcript_succ i, fst_PrvState_succ' P i]) ?_ ?_
    · have hαeq : ((pSpec₁ ++ₚ pSpec₂).Challenge ⟨Fin.castLE (show m ≤ m + n by omega) i, hDir⟩
            → P.PrvState (Fin.castLE (show m ≤ m + n by omega) i).succ)
          = (pSpec₁.Challenge ⟨i, hDir₁⟩ → (Prover.fst P).PrvState i.succ) := by
        rw [hChalEq, fst_PrvState_succ' P i]
      change HEq (OracleComp.liftComp
              (P.receiveChallenge ⟨Fin.castLE (show m ≤ m + n by omega) i, hDir⟩ s)
              (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
          (OracleComp.liftComp
            (OracleComp.liftComp ((Prover.fst P).receiveChallenge ⟨i, hDir₁⟩ s')
              (oSpec + [pSpec₁.Challenge]ₒ))
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
      rw [liftComp_liftComp (spec := oSpec) (midSpec := oSpec + [pSpec₁.Challenge]ₒ)
        (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)
        ((Prover.fst P).receiveChallenge ⟨i, hDir₁⟩ s')]
      exact liftComp_heq_congr (spec := oSpec)
        (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hαeq hrecvBase
    · rintro fA f₁ hf
      refine pure_heq_pure (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        (by rw [append_Transcript_succ i, fst_PrvState_succ' P i]) ?_
      refine prodMk_heq (append_Transcript_succ i) (fst_PrvState_succ' P i) ?_ ?_
      · exact concat_heq i ht hchal
      · refine heq_app hChalEq ?_ hf hchal
        rw [hChalEq, fst_PrvState_succ' P i]

open OracleComp in
/-- **Phase-1 faithfulness.** `P`'s run up to a left round `castLE j` equals (heterogeneously, after
lifting the phase-1 challenge oracle) the phase-1 restriction's run up to round `j`. -/
theorem fst_runToRound_heq (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmt : Stmt₁) (wit : Wit₁) (j : Fin (m + 1)) :
    HEq (P.runToRound (Fin.castLE (show m + 1 ≤ m + n + 1 by omega) j) stmt wit)
        (liftM ((Prover.fst P).runToRound j stmt wit) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
  induction j using Fin.induction with
  | zero =>
    rw [show ((0 : Fin (m + 1)).castLE (show m + 1 ≤ m + n + 1 by omega) : Fin (m + n + 1)) = 0
          from by ext; simp]
    rw [Prover.runToRound_zero_of_prover_first, Prover.runToRound_zero_of_prover_first, liftM_pure]
    have hT : Transcript 0 (pSpec₁ ++ₚ pSpec₂) = Transcript 0 pSpec₁ := by
      unfold ProtocolSpec.Transcript ProtocolSpec.FullTranscript
      apply pi_congr; intro i; exact absurd i.isLt (by simp)
    have hS : P.PrvState 0 = (Prover.fst P).PrvState 0 := rfl
    apply pure_heq_pure
    · rw [hT, hS]
    · apply prodMk_heq
      · exact hT
      · exact hS
      · exact Subsingleton.helim hT _ _
      · exact HEq.rfl
  | succ i ih =>
    have hidx : ((i.succ).castLE (show m + 1 ≤ m + n + 1 by omega) : Fin (m + n + 1))
        = (i.castLE (show m ≤ m + n by omega)).succ := by ext; simp
    rw [hidx, Prover.runToRound_succ]
    rw [Prover.runToRound_succ]
    have hcur : HEq (P.runToRound (i.castLE (show m ≤ m + n by omega)).castSucc stmt wit)
        (liftM ((Prover.fst P).runToRound i.castSucc stmt wit) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
      have hcastSucc : (i.castSucc.castLE (show m + 1 ≤ m + n + 1 by omega) : Fin (m + n + 1))
          = (i.castLE (show m ≤ m + n by omega)).castSucc := by ext; simp
      rw [← hcastSucc]; exact ih
    cases hd : pSpec₁.dir i with
    | V_to_P =>
      exact fst_processRound_left_challenge P i hd
        (P.runToRound (i.castLE (show m ≤ m + n by omega)).castSucc stmt wit)
        ((Prover.fst P).runToRound i.castSucc stmt wit) hcur
    | P_to_V =>
      exact fst_processRound_left_message P i hd
        (P.runToRound (i.castLE (show m ≤ m + n by omega)).castSucc stmt wit)
        ((Prover.fst P).runToRound i.castSucc stmt wit) hcur

/-- **Right-round `sendMessage` faithfulness for `snd`** (natAdd analogue of `fst_sendMessage_left`). -/
theorem snd_sendMessage_natAdd (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (k : Fin n)
    (hDir' : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .P_to_V)
    (hDir : pSpec₂.dir k = .P_to_V)
    (state : P.PrvState (Fin.natAdd m k).castSucc) :
    HEq (P.sendMessage ⟨Fin.natAdd m k, hDir'⟩ state)
        ((Prover.snd P).sendMessage ⟨k, hDir⟩
          (cast (congrArg P.PrvState
                  (show ((Fin.natAdd m k).castSucc) = Fin.natAdd m k.castSucc from by ext; simp))
                state)) := by
  dsimp only [Prover.snd]
  refine (HEq.trans (map_heq_self ?_ _ _ ?_)
    (sendMessage_heq_congr rfl (cast_heq _ _))).symm
  · rw [append_Message_natAdd k hDir' hDir]; congr 1
  · rintro ⟨msg, st⟩
    exact prodMk_heq (append_Message_natAdd k hDir' hDir).symm rfl (cast_heq _ _) HEq.rfl

/-- **Right-round `receiveChallenge` faithfulness for `snd`.** -/
theorem snd_receiveChallenge_natAdd (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (k : Fin n)
    (hDir' : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .V_to_P)
    (hDir : pSpec₂.dir k = .V_to_P)
    (state : P.PrvState (Fin.natAdd m k).castSucc) :
    HEq (P.receiveChallenge ⟨Fin.natAdd m k, hDir'⟩ state)
        ((Prover.snd P).receiveChallenge ⟨k, hDir⟩
          (cast (congrArg P.PrvState
                  (show ((Fin.natAdd m k).castSucc) = Fin.natAdd m k.castSucc from by ext; simp))
                state)) := by
  have hChal : (pSpec₁ ++ₚ pSpec₂).Challenge ⟨Fin.natAdd m k, hDir'⟩
      = pSpec₂.Challenge ⟨k, hDir⟩ := append_Challenge_natAdd k hDir' hDir
  dsimp only [Prover.snd]
  refine (HEq.trans (map_heq_self ?_ _ _ ?_)
    (receiveChallenge_heq_congr rfl (cast_heq _ _))).symm
  · rw [hChal]; congr 1
  · intro f
    refine Function.hfunext hChal.symm ?_
    intro c c' hcc
    have hc : cast hChal.symm c = c' := eq_of_heq ((cast_heq _ _).trans hcc)
    rw [hc]

/-- **Left-region merge.** Over the left-half round indices, `P`'s run agrees with the run of the
append of its own seam restrictions `(fst P).append (snd P)` (both over the appended protocol, so the
transcripts match in type; only `PrvState` differs). Transitivity of phase-1 faithfulness
(`fst_runToRound_heq`) and the existing `append_runToRound_left`. The right-region/full merge splits
at the seam via `runToRound_eq_bind_continueFromTo` and folds the right block using
`append_sendMessage_natAdd` composed with `snd_sendMessage_natAdd` (both sides append-protocol, so no
transcript-suffix mismatch). -/
theorem merge_runToRound_castLE (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmt : Stmt₁) (wit : Wit₁) (j : Fin (m + 1)) :
    HEq (P.runToRound (Fin.castLE (show m + 1 ≤ m + n + 1 by omega) j) stmt wit)
        (((Prover.fst P).append (Prover.snd P)).runToRound
          (Fin.castLE (show m + 1 ≤ m + n + 1 by omega) j) stmt wit) :=
  (fst_runToRound_heq P stmt wit j).trans
    (append_runToRound_left (P₁ := Prover.fst P) (P₂ := Prover.snd P) j).symm

/-- **Right-interior per-round sendMessage merge** (`k > 0`): the append-of-restrictions and `P`
agree on `sendMessage` at a right round, via `snd` as the pivot
(`append_sendMessage_natAdd` then `snd_sendMessage_natAdd`). -/
theorem merge_sendMessage_natAdd (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (k : Fin n) (hk : 0 < (k : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .P_to_V)
    (hDir₂ : pSpec₂.dir k = .P_to_V)
    (stateA : ((Prover.fst P).append (Prover.snd P)).PrvState (Fin.natAdd m k).castSucc)
    (stateP : P.PrvState (Fin.natAdd m k).castSucc)
    (hst : HEq stateA stateP) :
    HEq (((Prover.fst P).append (Prover.snd P)).sendMessage ⟨Fin.natAdd m k, hDir⟩ stateA)
        (P.sendMessage ⟨Fin.natAdd m k, hDir⟩ stateP) := by
  refine (append_sendMessage_natAdd (P₁ := Prover.fst P) (P₂ := Prover.snd P)
    k hk hDir hDir₂ stateA).trans ?_
  refine (sendMessage_heq_congr (P := Prover.snd P) rfl ?_).trans
    (snd_sendMessage_natAdd P k hDir hDir₂ stateP).symm
  exact (cast_heq _ _).trans (hst.trans (cast_heq _ _).symm)

/-- **Right-interior per-round receiveChallenge merge** (`k > 0`). -/
theorem merge_receiveChallenge_natAdd (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (k : Fin n) (hk : 0 < (k : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .V_to_P)
    (hDir₂ : pSpec₂.dir k = .V_to_P)
    (stateA : ((Prover.fst P).append (Prover.snd P)).PrvState (Fin.natAdd m k).castSucc)
    (stateP : P.PrvState (Fin.natAdd m k).castSucc)
    (hst : HEq stateA stateP) :
    HEq (((Prover.fst P).append (Prover.snd P)).receiveChallenge ⟨Fin.natAdd m k, hDir⟩ stateA)
        (P.receiveChallenge ⟨Fin.natAdd m k, hDir⟩ stateP) := by
  refine (append_receiveChallenge_natAdd (P₁ := Prover.fst P) (P₂ := Prover.snd P)
    k hk hDir hDir₂ stateA).trans ?_
  refine (receiveChallenge_heq_congr (P := Prover.snd P) rfl ?_).trans
    (snd_receiveChallenge_natAdd P k hDir hDir₂ stateP).symm
  exact (cast_heq _ _).trans (hst.trans (cast_heq _ _).symm)

/-- State-type eq at a right-interior `castSucc` (k>0): the append-of-restrictions and `P` agree. -/
theorem merge_PrvState_natAdd_castSucc (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (k : Fin n) (hk : 0 < (k : ℕ)) :
    ((Prover.fst P).append (Prover.snd P)).PrvState (Fin.natAdd m k).castSucc
      = P.PrvState (Fin.natAdd m k).castSucc :=
  (append_PrvState_natAdd_castSucc (P₁ := Prover.fst P) (P₂ := Prover.snd P) k hk).trans
    (congrArg P.PrvState (by ext; simp))

/-- State-type eq at a right-interior `succ`. -/
theorem merge_PrvState_natAdd_succ (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (k : Fin n) :
    ((Prover.fst P).append (Prover.snd P)).PrvState (Fin.natAdd m k).succ
      = P.PrvState (Fin.natAdd m k).succ := by
  rw [show (Fin.natAdd m k).succ = (Fin.natAdd (m+1) k).cast (by omega) from by ext; simp; omega]
  rw [append_PrvState_natAdd_succ (P₁ := Prover.fst P) (P₂ := Prover.snd P) k]
  exact congrArg P.PrvState (by ext; simp; omega)

/-- **Right-interior per-round processRound merge (message branch, k>0).** Both sides are over the
appended protocol, so transcripts match in type; `sendMessage` agreement is `merge_sendMessage_natAdd`
lifted via `liftComp_heq_congr`. -/
theorem merge_processRound_natAdd_message
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (k : Fin n) (hk : 0 < (k : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .P_to_V)
    (curA : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m k).castSucc
        × ((Prover.fst P).append (Prover.snd P)).PrvState (Fin.natAdd m k).castSucc))
    (curP : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m k).castSucc
        × P.PrvState (Fin.natAdd m k).castSucc))
    (hcur : HEq curA curP) :
    HEq (((Prover.fst P).append (Prover.snd P)).processRound (Fin.natAdd m k) curA)
        (P.processRound (Fin.natAdd m k) curP) := by
  have hDir₂ : pSpec₂.dir k = .P_to_V := by rw [← append_dir_natAdd (pSpec₁ := pSpec₁)]; exact hDir
  rw [processRound_message ((Prover.fst P).append (Prover.snd P)) (Fin.natAdd m k) hDir curA,
    processRound_message P (Fin.natAdd m k) hDir curP]
  refine bind_heq_congr (by rw [merge_PrvState_natAdd_castSucc P k hk])
    (by rw [merge_PrvState_natAdd_succ P k]) hcur ?_
  rintro ⟨t, s⟩ ⟨t', s'⟩ hr
  obtain ⟨ht, hs⟩ := prod_heq_split rfl (merge_PrvState_natAdd_castSucc P k hk) hr
  dsimp only
  refine bind_heq_congr (by rw [merge_PrvState_natAdd_succ P k])
    (by rw [merge_PrvState_natAdd_succ P k])
    (liftComp_heq_congr (spec := oSpec) (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (by rw [merge_PrvState_natAdd_succ P k])
      (merge_sendMessage_natAdd P k hk hDir hDir₂ s s' hs)) ?_
  rintro ⟨msg, ns⟩ ⟨msg', ns'⟩ hmsg
  obtain ⟨hm, hns⟩ := prod_heq_split rfl (merge_PrvState_natAdd_succ P k) hmsg
  refine pure_heq_pure (by rw [merge_PrvState_natAdd_succ P k]) ?_
  refine prodMk_heq rfl (merge_PrvState_natAdd_succ P k) ?_ hns
  rw [eq_of_heq hm, eq_of_heq ht]

/-- **Right-interior per-round processRound merge (challenge branch, k>0).** -/
theorem merge_processRound_natAdd_challenge
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (k : Fin n) (hk : 0 < (k : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .V_to_P)
    (curA : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m k).castSucc
        × ((Prover.fst P).append (Prover.snd P)).PrvState (Fin.natAdd m k).castSucc))
    (curP : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m k).castSucc
        × P.PrvState (Fin.natAdd m k).castSucc))
    (hcur : HEq curA curP) :
    HEq (((Prover.fst P).append (Prover.snd P)).processRound (Fin.natAdd m k) curA)
        (P.processRound (Fin.natAdd m k) curP) := by
  have hDir₂ : pSpec₂.dir k = .V_to_P := by rw [← append_dir_natAdd (pSpec₁ := pSpec₁)]; exact hDir
  rw [processRound_challenge' ((Prover.fst P).append (Prover.snd P)) (Fin.natAdd m k) hDir curA,
    processRound_challenge' P (Fin.natAdd m k) hDir curP]
  refine bind_heq_congr (by rw [merge_PrvState_natAdd_castSucc P k hk])
    (by rw [merge_PrvState_natAdd_succ P k]) hcur ?_
  rintro ⟨t, s⟩ ⟨t', s'⟩ hr
  obtain ⟨ht, hs⟩ := prod_heq_split rfl (merge_PrvState_natAdd_castSucc P k hk) hr
  dsimp only
  refine bind_heq_congr rfl (by rw [merge_PrvState_natAdd_succ P k]) HEq.rfl ?_
  rintro chal chal' hchal
  refine bind_heq_congr (by rw [merge_PrvState_natAdd_succ P k])
    (by rw [merge_PrvState_natAdd_succ P k])
    (liftComp_heq_congr (spec := oSpec) (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (by rw [merge_PrvState_natAdd_succ P k])
      (merge_receiveChallenge_natAdd P k hk hDir hDir₂ s s' hs)) ?_
  rintro fA f' hf
  refine pure_heq_pure (by rw [merge_PrvState_natAdd_succ P k]) ?_
  refine prodMk_heq rfl (merge_PrvState_natAdd_succ P k) ?_ ?_
  · rw [eq_of_heq hchal, eq_of_heq ht]
  · refine heq_app rfl ?_ hf hchal
    rw [merge_PrvState_natAdd_succ P k]

end Prover
