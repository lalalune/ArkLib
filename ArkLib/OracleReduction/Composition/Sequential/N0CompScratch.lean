import ArkLib.OracleReduction.Composition.Sequential.EmptyAppend
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
  rw [Reduction.run_of_append_empty]
  trace_state
  sorry

end Reduction
