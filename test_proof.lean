import ArkLib.ToMathlib.SpartanBricks

open Spartan Spec Bricks CheckClaim OracleReduction

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [SampleableType R] {pp : PublicParams}
variable {ι : Type} {oSpec : OracleSpec ι}
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

lemma checkClaim_completeness (hInit : NeverFail init) :
    (finalCheck R pp oSpec).perfectCompleteness init impl (finalCheckRelIn R pp) (finalCheckRelOut R pp) := by
  simp only [OracleReduction.perfectCompleteness, Reduction.perfectCompleteness_eq_prob_one]
  intro x hx
  obtain ⟨⟨stmt, oStmt⟩, wit⟩ := x
  simp only [finalCheckRelIn, Set.mem_setOf_eq] at hx
  simp only [finalCheck, CheckClaim.oracleReduction, OracleReduction.toReduction, Prover.run, Verifier.run, CheckClaim.oracleProver, CheckClaim.oracleVerifier, bind_pure_comp, Functor.map_map]
  have hguard : (do let _ ← Spartan.Spec.finalCheckPred R pp stmt; return stmt : OptionT (OracleComp oSpec) _) = pure stmt := by
    dsimp [Spartan.Spec.finalCheckPred] at hx ⊢
    simp [guard, if_pos hx]
    rfl
  simp only [hguard, simulateQ_map, simulateQ_pure, StateT.run_map, StateT.run_pure, Functor.map_map, Function.comp_apply]
  simp [probEvent_pure]

