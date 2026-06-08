import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessMsg
import ArkLib.ToVCVio.Lemmas

open OracleComp OracleSpec ProtocolSpec
namespace KGrind5
variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

example
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (stmt : Stmt₁) (wit : Wit₁)
    (x : (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃) × Stmt₃)
    (hx : some x ∈ support (m := OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
      (α := Option _) ((R₁.append R₂).run stmt wit)) : True := by
  rw [Reduction.run, Reduction.append] at hx
  simp only [Prover.append_run_msg _ _ hn hDir hDir₂,
    OptionT.mem_support_OptionT_bind_run_some_iff] at hx
  extract_goal
  trivial
end KGrind5
