import ArkLib.OracleReduction.Composition.Sequential.EmptyAppend

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

-- First: a clean run-factoring of the appended reduction's run (raw, no interpretation).
theorem run_append_empty (stmt : Stmt₁) (wit : Wit₁) :
    (R₁.append R₂).run stmt wit = (do
      let prv ← (R₁.prover.append R₂.prover).run stmt wit
      let stmtOut ← liftM ((R₁.verifier.append R₂.verifier).run stmt prv.1).run
      return ⟨prv, ← stmtOut.getM⟩) := rfl

end Reduction
