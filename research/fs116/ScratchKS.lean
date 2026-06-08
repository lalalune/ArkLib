import ArkLib.OracleReduction.FiatShamir.StateRestorationTransport

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

attribute [local instance] Reduction.fiatShamirChallengeOracleInterface

variable {ι : Type} {oSpec : OracleSpec ι}
variable {StmtIn WitIn StmtOut WitOut : Type}
variable {n : ℕ} {pSpec : ProtocolSpec n}
variable [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)]
variable [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]

section Probe

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

private theorem stateT_option_bind_map_eq
    {σ α β γ : Type} (mx : StateT σ ProbComp (Option α)) (f : α → β)
    (k : β → StateT σ ProbComp (Option γ)) :
    (mx >>= fun oa => match oa with
      | none => pure none
      | some a => k (f a)) =
    ((Option.map f <$> mx) >>= fun ob => match ob with
      | none => pure none
      | some b => k b) := by
  apply StateT.ext
  intro s
  simp only [StateT.run_bind, StateT.run_map]
  rw [bind_map_left]
  apply bind_congr
  intro x
  cases x with
  | mk oa s' =>
      cases oa <;> rfl

private theorem stateT_option_elimM_map_eq
    {σ α β γ : Type} (mx : StateT σ ProbComp (Option α)) (f : α → β)
    (k : β → StateT σ ProbComp (Option γ)) :
    Option.elimM mx (pure none) (fun a => k (f a)) =
      Option.elimM (Option.map f <$> mx) (pure none) k := by
  unfold Option.elimM
  exact stateT_option_bind_map_eq mx f k

private theorem scratch_probEvent_optionT_stateT_init
    {σ α : Type} (init : ProbComp σ) (comp : StateT σ ProbComp (Option α))
    (p : α → Prop) :
    Pr[p | (do
        let s ← OptionT.mk (some <$> init)
        OptionT.mk ((fun x : Option α × σ => x.1) <$> comp.run s) : OptionT ProbComp α)] =
      Pr[fun o : Option α => o.elim False p |
        do
          let s ← init
          (fun x : Option α × σ => x.1) <$> comp.run s] := by
  rw [show
      (do
        let s ← OptionT.mk (some <$> init)
        OptionT.mk ((fun x : Option α × σ => x.1) <$> comp.run s) : OptionT ProbComp α) =
      OptionT.mk (do
        let s ← init
        (fun x : Option α × σ => x.1) <$> comp.run s) by
    apply OptionT.ext
    simp only [OptionT.run_bind, OptionT.run_mk, Option.elimM, bind_assoc, map_bind,
      Option.elim_some, pure_bind]
    rw [map_eq_pure_bind]
    simp only [bind_assoc, pure_bind, Option.elim_some]]
  exact Verifier.StateFunction.probEvent_optionT_mk_eq_elim _ _

local instance fiatShamirProverOnlyCanonicalKSScratch : ProtocolSpec.ProverOnly
    (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)) where
  prover_first' := by simp

theorem scratch_fiatShamirKnowledgeExec_runCollapse
    {σ : Type}
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn StmtOut WitOut
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        ((do
          let d ← Reduction.runWithLog stmtIn witIn
            { prover := P, verifier := V.fiatShamir }
          let extractedWitIn ←
            liftM do
              let transcript ← OptionT.mk (some <$> Messages.deriveTranscriptFS
                (oSpec := oSpec) stmtIn (d.1.1.1 0))
              liftM (srExtractor stmtIn d.1.1.2.2 transcript default default)
          pure (stmtIn, extractedWitIn, d.1.2, d.1.1.2.2)).run) =
      simulateQ impl
        ((do
          let d ← fiatShamirAdversaryExecution P V stmtIn witIn
          let extractedWitIn ←
            liftM do
              let transcript ← OptionT.mk (some <$> Messages.deriveTranscriptFS
                (oSpec := oSpec) stmtIn (d.1.1 0))
              liftM (srExtractor stmtIn d.1.2.2 transcript default default)
          pure (stmtIn, extractedWitIn, d.2, d.1.2.2)).run) := by
  simp only [OptionT.run_bind, simulateQ_option_elimM, simulateQ_pure]
  rw [stateT_option_elimM_map_eq
    (f := Prod.fst)
    (k := fun d =>
      Option.elimM
        (simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          (liftM do
              let transcript ← OptionT.mk (some <$> Messages.deriveTranscriptFS
                (oSpec := oSpec) stmtIn (d.1.1 0))
              liftM (srExtractor stmtIn d.1.2.2 transcript default default)).run)
        (pure none) fun extractedWitIn =>
          simulateQ (QueryImpl.addLift impl challengeQueryImpl)
            (pure (stmtIn, extractedWitIn, d.2, d.1.2.2)).run)]
  rw [fiatShamir_runWithLog_simulateQ_fst impl P V stmtIn witIn]

theorem scratch_fiatShamir_knowledgeSoundnessTransferResidual_canonical
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (knowledgeError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl srInit
      (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
      relIn relOut knowledgeError V := by
  intro hSR
  obtain ⟨srExtractor, hSR⟩ := hSR
  refine ⟨fiatShamirStraightlineExtractorOfStateRestoration
      (oSpec := oSpec) (pSpec := pSpec) srExtractor, ?_⟩
  intro stmtIn witIn prover
  have h :=
    hSR (Prover.StateRestoration.knowledgeSoundnessOfFiatShamirProver
      (oSpec := oSpec) (pSpec := pSpec) prover stmtIn witIn)
  dsimp only
  simp [fiatShamirStraightlineExtractorOfStateRestoration]
  rw [scratch_probEvent_optionT_stateT_init]
  refine le_trans ?_ h
  simp [Verifier.StateRestoration.srKnowledgeSoundnessGame_eq_deriveTranscriptFS,
    Prover.StateRestoration.knowledgeSoundnessOfFiatShamirProver,
    fiatShamirCoupledQueryImpl,
    ProtocolSpec.fsChallengeQueryImplState_eq_srChallengeQueryImpl',
    probEvent_map, map_bind, Functor.map_map, Function.comp,
    StateT.run_bind, StateT.run_map,
    Verifier.fiatShamir_verify_eq,
    Reduction.fiatShamir, Prover.fiatShamir, Verifier.fiatShamir,
    Reduction.run, Prover.run, Prover.runToRound, Prover.processRound]

end Probe

end Reduction
