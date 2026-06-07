import ArkLib.ToMathlib.ZKDefA
noncomputable section
open OracleComp OracleSpec ProtocolSpec
namespace Reduction
variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn : Type} {σ : Type}
example (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmtIn : StmtIn) (witIn : WitIn) :
    honestTranscriptDist init impl
        (Reduction.id : Reduction oSpec StmtIn WitIn StmtIn WitIn !p[]) stmtIn witIn =
      (pure default : OptionT ProbComp (FullTranscript !p[])) := by
  unfold honestTranscriptDist
  simp only [Reduction.id_run]
  trace_state
  sorry
end Reduction
