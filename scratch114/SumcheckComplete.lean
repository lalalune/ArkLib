import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeMsgCompleteness
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessEmpty

/-!
Scratch: full multi-round sum-check perfect completeness (Reduction level), assembling
`Reduction.seqCompose_perfectCompleteness_of_append_msg` (n-ary) +
`reduction_append_perfectCompleteness_msg` / `append_perfectCompleteness_empty_proof` (binary
keystones) + per-round `SingleRound.reduction_perfectCompleteness`.
-/

open ProtocolSpec OracleComp OracleSpec
open scoped NNReal

namespace Sumcheck.Spec

variable {R : Type} [CommSemiring R] [SampleableType R] [DecidableEq R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

set_option maxHeartbeats 1000000 in
/-- **Full multi-round sum-check perfect completeness (Reduction level).** -/
theorem reduction_perfectCompleteness (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (reduction R deg D n oSpec).perfectCompleteness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (Fin.last n)) := by
  apply Reduction.seqCompose_perfectCompleteness_of_append_msg
    (Stmt := fun i => StatementRound R n i × (∀ j, OracleStatement R n deg j))
    (Wit := fun _ => Unit)
    (R := SingleRound.reduction R n deg D oSpec)
    (rel := fun i => relationRound R n deg D i)
  · -- hAppend: discharge both seam shapes
    intro S₁ W₁ S₂ W₂ S₃ W₃ k₁ k₂ p₁ p₂ _ _ R₁ R₂ r₁ r₂ r₃ hvalid hc₁ hc₂
    rcases hvalid with rfl | ⟨hpos, hdir⟩
    · exact Reduction.append_perfectCompleteness_empty_proof R₁ R₂ hc₁ hc₂ hInit hImplSupp
    · refine Reduction.reduction_append_perfectCompleteness_msg R₁ R₂ hc₁ hc₂ hpos ?_ hdir hInit
        hImplSupp
      rw [show (⟨k₁, by omega⟩ : Fin (k₁ + k₂)) = Fin.natAdd k₁ ⟨0, hpos⟩ from by ext; simp,
        Prover.append_dir_natAdd]
      exact hdir
  · -- hValid: each round starts with the prover's P_to_V message
    intro _
    exact ⟨by omega, by decide⟩
  · -- h: per-round completeness
    intro i
    exact SingleRound.reduction_perfectCompleteness R n deg D oSpec i

end Sumcheck.Spec
