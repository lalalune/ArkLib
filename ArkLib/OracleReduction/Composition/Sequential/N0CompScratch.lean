import ArkLib.OracleReduction.Composition.Sequential.EmptyAppendReduction
import ArkLib.ToVCVio.OracleComp.SimSemantics.SubsingletonState

open OracleSpec OracleComp ProtocolSpec
open scoped NNReal ENNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {init : ProbComp Unit} {impl : QueryImpl oSpec (StateT Unit ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
  {R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
  {R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}

example
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  unfold perfectCompleteness at h₁ h₂ ⊢
  rw [completeness_iff_completenessFromRun] at h₁ h₂ ⊢
  unfold completenessFromRun at h₁ h₂ ⊢
  intro stmt wit hmem
  dsimp only
  rw [run_append_empty]
  simp only [ENNReal.coe_zero, tsub_zero, ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · sorry
  · intro out hout
    rw [OptionT.mem_support_iff] at hout
    simp only [OptionT.run_mk] at hout
    rw [mem_support_bind_iff] at hout
    obtain ⟨u, _hu, hout⟩ := hout
    simp only [OptionT.run_bind, OptionT.run_pure, bind_assoc, Option.elimM] at hout
    rw [simulateQ_run'_bind_of_subsingleton, mem_support_bind_iff] at hout
    obtain ⟨p1, hp1, hout⟩ := hout
    rcases p1 with _ | pr1
    · simp only [Option.elim_none, simulateQ_pure, StateT.run'_eq, StateT.run_pure,
        map_pure, support_pure, Set.mem_singleton_iff, reduceCtorEq] at hout
    · simp only [Option.elim_some] at hout
      rw [simulateQ_run'_bind_of_subsingleton, mem_support_bind_iff] at hout
      obtain ⟨p2, hp2, hout⟩ := hout
      rcases p2 with _ | pr2
      · simp only [Option.elim_none, simulateQ_pure, StateT.run'_eq, StateT.run_pure,
        map_pure, support_pure, Set.mem_singleton_iff, reduceCtorEq] at hout
      · simp only [Option.elim_some] at hout
        -- split the appended verifier V₁;V₂ and peel
        rw [Verifier.append_run] at hout
        simp only [OptionT.run_bind, OptionT.run_pure, OptionT.run_lift, bind_assoc,
          Option.elimM] at hout
        rw [simulateQ_run'_bind_of_subsingleton, mem_support_bind_iff] at hout
        obtain ⟨v1, hv1, hout⟩ := hout
        rcases v1 with _ | sv1
        · simp only [Option.elim_none, simulateQ_pure, StateT.run'_eq, StateT.run_pure,
            map_pure, support_pure, Set.mem_singleton_iff, reduceCtorEq] at hout
        · simp only [Option.elim_some] at hout
          simp only [OracleComp.liftComp_eq_liftM] at hv1
          rw [simulateQ_run'_bind_of_subsingleton, mem_support_bind_iff] at hv1
          trace_state
          sorry

end Reduction
