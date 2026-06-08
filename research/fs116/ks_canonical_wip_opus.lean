import ArkLib.OracleReduction.FiatShamir.StateRestorationTransport

open ProtocolSpec OracleComp OracleSpec
open scoped NNReal

namespace Reduction

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

attribute [local instance 10000] Reduction.fiatShamirNoChallengeSampleable

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

local instance fiatShamirProverOnlyCanonicalKSwip : ProtocolSpec.ProverOnly
    (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)) where
  prover_first' := by simp

/-- Generic: a `Reduction.run`-bind equals a `runWithLog`-bind whose continuation only consumes the
run result (discarding logs). The easy (no-HOU) direction proven by rewriting `run`. -/
theorem bind_run_eq_bind_runWithLog_fst
    {γ : Type} (red : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (F : ((pSpec.FullTranscript × StmtOut × WitOut) × StmtOut) →
         OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) γ) :
    (Reduction.run stmt wit red >>= F) =
      (Reduction.runWithLog stmt wit red >>= fun d => F d.1) := by
  rw [← Reduction.runWithLog_discard_logs_eq_run (reduction := red)]
  rw [map_eq_pure_bind, bind_assoc]
  simp only [pure_bind]

/-- The canonical Fiat-Shamir straightline extractor ignores its query-log arguments. -/
theorem fiatShamirStraightlineExtractorOfStateRestoration_log_irrel
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (stmtIn : StmtIn) (witOut : WitOut)
    (proof : FullTranscript (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (pLog vLog pLog' vLog' :
      QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :
    fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof pLog vLog =
      fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof pLog' vLog' :=
  rfl

theorem fiatShamir_knowledgeSoundnessTransferResidual_canonical_wip
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
  obtain ⟨srExtractor, hbound⟩ := hSR
  refine ⟨fiatShamirStraightlineExtractorOfStateRestoration
    (oSpec := oSpec) (pSpec := pSpec) srExtractor, ?_⟩
  intro stmtIn witIn prover
  have h := hbound (Prover.StateRestoration.knowledgeSoundnessOfFiatShamirProver
    (oSpec := oSpec) (pSpec := pSpec) prover stmtIn witIn)
  dsimp only
  refine le_trans ?_ h
  rw [fiatShamirStraightlineExtractorOfStateRestoration_log_irrel
    (pLog' := default) (vLog' := default)]
  sorry

end Reduction
