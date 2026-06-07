import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.Security.StateRestoration
import ArkLib.OracleReduction.LiftContext.Reduction
import ArkLib.OracleReduction.Security.RoundByRound

/-! WIP (#116B): coupled FS soundness transfer — full normalization attempt. NOT in build. -/

noncomputable section
open ProtocolSpec OracleComp OracleSpec
open scoped NNReal

-- Reconstructed (de-privatized) CompletenessAux helpers needed by the normalization.
namespace FS116Aux
variable {M : Type → Type} {α β : Type}

theorem liftM_eq_monadLift {m n : Type → Type} [MonadLiftT m n] (x : m α) :
    (liftM x : n α) = monadLift x := rfl

theorem optionT_lift_run_bind_getM [Monad M] [LawfulMonad M] (X : OptionT M α) :
    ((liftM X.run : OptionT M (Option α)) >>= fun o => (o.getM : OptionT M α)) = X := by
  apply OptionT.ext
  simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_assoc,
    map_eq_pure_bind, pure_bind]
  conv_rhs => rw [← bind_pure X.run]
  congr 1
  funext o
  cases o <;> rfl

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}

theorem monadLift_optionT_lift_run_getM (X : OptionT (OracleComp spec₁) α) :
    ((monadLift (liftM X.run : OptionT (OracleComp spec₁) (Option α)) :
          OptionT (OracleComp (spec₁ + spec₂)) (Option α)) >>=
        fun o => (o.getM : OptionT (OracleComp (spec₁ + spec₂)) α)) =
      (monadLift X : OptionT (OracleComp (spec₁ + spec₂)) α) := by
  conv_rhs => rw [← optionT_lift_run_bind_getM X]
  rw [monadLift_bind]
  congr 1
  funext o
  cases o <;> rfl

theorem monadLift_optionT_lift_run_map_getM (X : OptionT (OracleComp spec₁) β) (f : β → α) :
    ((monadLift (liftM X.run : OptionT (OracleComp spec₁) (Option β)) :
          OptionT (OracleComp (spec₁ + spec₂)) (Option β)) >>=
        fun o => f <$> (o.getM : OptionT (OracleComp (spec₁ + spec₂)) β)) =
      (f <$> (monadLift X : OptionT (OracleComp (spec₁ + spec₂)) β) :
        OptionT (OracleComp (spec₁ + spec₂)) α) := by
  simp only [← bind_pure_comp, ← bind_assoc, monadLift_optionT_lift_run_getM]

theorem liftM_optionT_combined (m : OracleComp spec₁ α) :
    (liftM m : OptionT (OracleComp (spec₁ + spec₂)) α) =
      (monadLift (liftM m : OptionT (OracleComp spec₁) α) :
        OptionT (OracleComp (spec₁ + spec₂)) α) := rfl

@[simp] theorem optionT_monadLift_run (x : OptionT (OracleComp spec₁) α) :
    ((monadLift x : OptionT (OracleComp (spec₁ + spec₂)) α)).run = monadLift x.run := rfl

theorem simulateQ_map_monadLift_getM_run {σ' : Type}
    (impl : QueryImpl (spec₁ + spec₂) (StateT σ' ProbComp)) (o : Option α) (f : α → β) :
    simulateQ impl
      ((f <$> (monadLift (o.getM : OptionT (OracleComp spec₁) α) :
          OptionT (OracleComp (spec₁ + spec₂)) α)).run) = pure (Option.map f o) := by
  have h : ((f <$> (monadLift (o.getM : OptionT (OracleComp spec₁) α) :
      OptionT (OracleComp (spec₁ + spec₂)) α)).run) = pure (Option.map f o) := by
    cases o <;> rfl
  rw [h, simulateQ_pure]

theorem optionT_run_simulateQ_liftquery (X : OptionT (OracleComp spec₁) α) :
    OptionT.run (simulateQ (fun t => (monadLift (OracleSpec.query t) :
        OracleComp (spec₁ + spec₂) _)) X) =
      (monadLift X.run : OracleComp (spec₁ + spec₂) (Option α)) := rfl

@[simp] theorem optionT_run_monadLift_oc
    [MonadLiftT (OracleComp spec₁) (OracleComp (spec₁ + spec₂))]
    (X : OracleComp spec₁ α) :
    (monadLift X : OptionT (OracleComp (spec₁ + spec₂)) α).run
      = OracleComp.liftComp (some <$> X) (spec₁ + spec₂) := rfl

theorem leaf_collapse {sigma : Type}
    [MonadLiftT (OracleComp spec₁) (OracleComp (spec₁ + spec₂))]
    (impl : QueryImpl spec₁ (StateT sigma ProbComp))
    (implC : QueryImpl spec₂ (StateT sigma ProbComp))
    (X : OracleComp spec₁ α) :
    simulateQ (impl + implC) ((monadLift X : OptionT (OracleComp (spec₁ + spec₂)) α).run)
      = some <$> simulateQ impl X := by
  have h : (monadLift X : OptionT (OracleComp (spec₁ + spec₂)) α).run
        = OracleComp.liftComp (some <$> X) (spec₁ + spec₂) := rfl
  rw [h, QueryImpl.simulateQ_add_liftComp_left, simulateQ_map]

end FS116Aux

open FS116Aux

namespace Reduction

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]

set_option maxHeartbeats 1000000 in
theorem fs116_coupled_final
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
  rw [Verifier.StateFunction.probEvent_optionT_mk_eq_elim]
  simp only [hsrProver, Verifier.fiatShamir_verify_eq, Verifier.run, bind_assoc, pure_bind,
    liftComp_eq_liftM]
  -- Full completeness-style normalization (both legs of fiatShamir_runCollapse's curated simp).
  simp only [Messages.deriveTranscriptFS, QueryImpl.addLift_def, QueryImpl.liftTarget_self,
    liftM_eq_monadLift, OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk,
    optionT_monadLift_run, simulateQ_bind, simulateQ_map, simulateQ_pure, simulateQ_addLift_liftM,
    OptionT.simulateQ_addLift_liftM, Option.getM_map_run, Option.elimM, simulateQ_option_elim,
    bind_assoc, pure_bind, map_bind, simulateQ_getM_run_some, OptionT.simulateQ_getM_some,
    StateT.run_simulateQ_optiont_map, StateT.run_pure_some_bind_map, Option.map_comp_lambda,
    simulateQ_map_monadLift_getM_run, optionT_run_simulateQ_liftquery]
  simp [simulateQ_bind, simulateQ_map, simulateQ_pure, simulateQ_addLift_liftM,
    OptionT.simulateQ_addLift_liftM, simulateQ_option_elim, simulateQ_getM_run_some,
    OptionT.simulateQ_getM_some, StateT.run_simulateQ_optiont_map, StateT.run_pure_some_bind_map,
    Option.getM_map_run, Option.map_comp_lambda, optionT_monadLift_run, liftM_eq_monadLift,
    OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk, monadLift_bind, monadLift_pure,
    Option.elimM, bind_assoc, pure_bind, map_bind]
  -- Build-verified to here. The remaining leaves are `simulateQ IMPL ((↑X).run)` where `↑` is a
  -- COERCION term (not literally `@monadLift`), so no simp/rw lemma matches; closing needs
  -- interactive per-leaf conv/change surgery in the nested-elim goal + a probEvent congruence.
  sorry

end Reduction
