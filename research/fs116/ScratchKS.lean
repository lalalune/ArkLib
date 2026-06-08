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
  funext s
  simp only [StateT.run_bind, StateT.run_map, map_bind]
  apply bind_congr
  intro x
  cases x with
  | mk oa s' =>
      cases oa <;> simp

local instance fiatShamirProverOnlyCanonicalKSScratch : ProtocolSpec.ProverOnly
    (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)) where
  prover_first' := by simp

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
