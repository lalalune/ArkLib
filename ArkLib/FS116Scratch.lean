import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.Security.StateRestoration
import ArkLib.OracleReduction.LiftContext.Reduction
import ArkLib.OracleReduction.Security.RoundByRound

/-! WIP (#116B): coupled FS soundness transfer. NOT in build. -/

noncomputable section
open ProtocolSpec OracleComp OracleSpec
open scoped NNReal

namespace Reduction

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]

axiom fiatShamir_soundness_of_stateRestoration_coupled
    (srInit : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (soundnessError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl langIn langOut V soundnessError) :
    Verifier.soundness srInit (srImpl.addLift srChallengeQueryImpl')
      langIn langOut V.fiatShamir soundnessError

end Reduction
