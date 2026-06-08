import ArkLib.OracleReduction.Composition.Sequential.AppendRunEvalDist
import ArkLib.OracleReduction.Completeness

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

example
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (stmtIn : Stmt₁) (witIn : Wit₁) :
    (R₁.append R₂).run stmtIn witIn = (do
        let proverResult ← liftM (((do
          let ⟨tr₁, s₂, w₂⟩ ← liftM (R₁.prover.run stmtIn witIn)
          let ⟨tr₂, s₃, w₃⟩ ← liftM (R₂.prover.run s₂ w₂)
          pure (tr₁ ++ₜ tr₂, s₃, w₃)) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃)))
        let stmtOut ← liftM ((R₁.append R₂).verifier.run stmtIn proverResult.1).run
        return (proverResult, ← stmtOut.getM)) := by
    unfold Reduction.run
    rw [show (R₁.append R₂).prover = R₁.prover.append R₂.prover from rfl,
      Prover.append_run_msg (P₁ := R₁.prover) (P₂ := R₂.prover) stmtIn witIn hn hDir hDir₂]
    rfl

end Reduction
