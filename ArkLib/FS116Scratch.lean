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

theorem fiatShamir_soundness_of_stateRestoration_coupled
    (srInit : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (soundnessError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl langIn langOut V soundnessError) :
    Verifier.soundness srInit (srImpl.addLift srChallengeQueryImpl')
      langIn langOut V.fiatShamir soundnessError := by
  classical
  haveI : ProtocolSpec.ProverOnly
      (⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩ : ProtocolSpec 1) :=
    { toProverFirst := { prover_first' := by simp } }
  intro WitIn' WitOut' witIn' prover stmtIn hstmtIn
  set srProver : Prover.StateRestoration.Soundness oSpec StmtIn pSpec :=
    (do
      let st := prover.input (stmtIn, witIn')
      let ⟨msg, st'⟩ ← prover.sendMessage ⟨0, by simp⟩ st
      let _ ← prover.output st'
      return (stmtIn, msg)) with hsrProver
  refine le_trans ?_ (hSR srProver)
  unfold srSoundnessGame
  rw [Reduction.run_of_prover_first]
  -- FS side: transport the OptionT probEvent to the underlying ProbComp (Option _).
  rw [Verifier.StateFunction.probEvent_optionT_mk_eq_elim]
  simp only [hsrProver, Verifier.fiatShamir_verify_eq, Verifier.run, bind_assoc, pure_bind,
    liftComp_eq_liftM]
  -- Now normalize: collapse empty FS-NI challenge oracle + push simulateQ; then reconcile events.
  simp only [Messages.deriveTranscriptFS, QueryImpl.addLift_def, QueryImpl.liftTarget_self,
    simulateQ_addLift_liftM, OptionT.simulateQ_addLift_liftM,
    simulateQ_bind, simulateQ_map, simulateQ_pure, simulateQ_getM_run_some, bind_assoc, pure_bind,
    map_bind, OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk, monadLift_bind,
    monadLift_pure, liftComp_eq_liftM]
  -- State after normalization: impl collapsed to `srImpl + srChallengeQueryImpl' +
  -- liftTarget challengeQueryImpl` over `Option.elimM` bind-chains whose leaves are `liftM`s over
  -- `oSpec + srChallengeOracle` (never the empty FS-NI challenge oracle).
  -- REMAINS: distribute `simulateQ` through the elimM/bind chains to the leaves (simulateQ_bind +
  -- Option.elimM lemmas), apply `simulateQ_addLift_liftM` at each leaf to drop `challengeQueryImpl`,
  -- then `probEvent` congruence — the SR predicate's `∧ stmtIn ∉ langIn` is closed by `hstmtIn`,
  -- and the discarded `ctxOut`/`prover.output` results marginalize out (the SR prover replays the
  -- same `output` step, so the StateT table-state evolution is identical). This mirrors the curated
  -- simp normalization in the proven completeness `fiatShamir_runCollapse`.
  sorry

end Reduction
