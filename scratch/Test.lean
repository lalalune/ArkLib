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

theorem run_eq_honestExecution
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Reduction.duplexSpongeFiatShamir_run_eq_honestExecution (U := U) R stmtIn witIn := by
  unfold Reduction.duplexSpongeFiatShamir_run_eq_honestExecution
  haveI : ProtocolSpec.ProverOnly ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩ := by
    exact { prover_first' := by simp }
  rw [Reduction.run_of_prover_first]
  unfold Reduction.duplexSpongeFiatShamirHonestExecution
  unfold Reduction.duplexSpongeFiatShamirHonestRun
  unfold Reduction.duplexSpongeFiatShamir
  unfold Reduction.prover Reduction.verifier
  unfold Prover.runToRoundDSFS
  -- Push liftM inside
  rw [OptionT.ext_iff]
  simp only [OptionT.run_liftM, OptionT.run_bind, bind_assoc, pure_bind, OracleComp.bind_pure_comp]
  simp only [OptionT.run_mk, Option.bind_some, Option.map_eq_map, Option.map_bind]
  congr
  ext x
  cases x
  rename_i msg state
  congr
  ext ctxOut
  congr
  ext stmtOut
  congr
  ext v
  cases v
  · rfl
  · rfl

