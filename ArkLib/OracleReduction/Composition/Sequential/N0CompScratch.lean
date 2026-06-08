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

-- Helper: a single reduction's experiment support membership decomposes (σ=Unit) into prover and
-- verifier outcome memberships. This is the reusable characterization for both R₁/R₂ and the
-- appended reduction.
example (R : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁) (stmt : Stmt₁) (wit : Wit₁)
    (u : Unit) (p : Option (pSpec₁.FullTranscript × Stmt₂ × Wit₂))
    (hp : p ∈ support ((simulateQ (impl.addLift challengeQueryImpl)
      (liftM (R.prover.run stmt wit)).run).run' u)) :
    ∃ pr, p = some pr := by
  simp only [OptionT.run_lift, simulateQ_map, StateT.run'_eq, StateT.run_map, map_map,
    support_map, Set.mem_image] at hp
  obtain ⟨a, _ha, rfl⟩ := hp
  exact ⟨_, rfl⟩

end Reduction
