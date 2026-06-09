import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessProof
import ArkLib.OracleReduction.Composition.Sequential.EmptyAppend

open OracleComp OracleSpec ProtocolSpec
namespace Reduction
variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

example
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁)
    (hmem0 : True)
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited] :
    True := by
  -- inspect the decomposed run shape
  have key : none ∈ support (OptionT.run ((R₁.append R₂).run stmt wit)) → True := by
    intro hmem0
    rw [Reduction.run, Reduction.append] at hmem0
    simp only [Prover.append_run_empty, Verifier.append_run,
      OptionT.run_bind, Option.elimM, bind_assoc, liftM_bind] at hmem0
    obtain ⟨a₁, hP₁, hmem0⟩ := (mem_support_bind_iff _ _ _).mp hmem0
    rcases a₁ with _ | ⟨tr₁, s₂, w₂⟩
    · trivial
    obtain ⟨a₂, hP₂, hmem0⟩ := (mem_support_bind_iff _ _ _).mp hmem0
    rcases a₂ with _ | ⟨tr₂, s₃, w₃⟩
    · trivial
    obtain ⟨a₃, hpr, hmem0⟩ := (mem_support_bind_iff _ _ _).mp hmem0
    rcases a₃ with _ | pr
    · trivial
    obtain ⟨a₄, hV₁, hmem0⟩ := (mem_support_bind_iff _ _ _).mp hmem0
    trace_state
    trivial
  trivial

end Reduction
