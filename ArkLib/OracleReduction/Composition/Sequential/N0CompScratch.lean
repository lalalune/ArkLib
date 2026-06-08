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
    -- peel P₁
    rw [simulateQ_run'_bind_of_subsingleton, mem_support_bind_iff] at hout
    obtain ⟨p1, hp1, hout⟩ := hout
    simp only [OptionT.run_lift, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map,
      support_map, Set.mem_image] at hp1
    obtain ⟨pr1, hpr1, rfl⟩ := hp1
    simp only [Option.elim] at hout
    -- peel P₂
    rw [simulateQ_run'_bind_of_subsingleton, mem_support_bind_iff] at hout
    obtain ⟨p2, hp2, hout⟩ := hout
    simp only [OptionT.run_lift, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map,
      support_map, Set.mem_image] at hp2
    obtain ⟨pr2, hpr2, rfl⟩ := hp2
    simp only [Option.elim] at hout
    trace_state
    sorry

end Reduction
