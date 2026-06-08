import ArkLib.OracleReduction.Composition.Sequential.EmptyAppend

open OracleSpec OracleComp ProtocolSpec scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
  (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
  (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)

example
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃) :
    reductionAppendPerfectCompletenessResidual R₁ R₂ h₁ h₂ := by
  unfold reductionAppendPerfectCompletenessResidual
  unfold Reduction.perfectCompleteness
  rw [completeness_iff_completenessFromRun]
  unfold completenessFromRun
  intro stmt wit hmem
  trace_state
  sorry

end Reduction
