import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Completeness
import ArkLib.OracleReduction.LiftContext.Reduction

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

theorem runCollapseResidual
    {σ : Type}
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Reduction.duplexSpongeFiatShamir_runCollapseResidual (U := U) impl R stmtIn witIn := by
  unfold Reduction.duplexSpongeFiatShamir_runCollapseResidual
  haveI : ProtocolSpec.ProverOnly ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩ := by
    exact { prover_first' := by simp }
  rw [Reduction.run_of_prover_first]
  -- assume we have the run_eq theorem
  sorry
