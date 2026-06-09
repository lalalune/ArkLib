import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeMsgCompleteness
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessMsg
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessEmpty

/-!
Scratch: full multi-round sum-check perfect completeness, assembling
`seqCompose_perfectCompleteness_of_append_msg` + the binary keystones
(`reduction_append_perfectCompleteness_msg` / `append_perfectCompleteness_empty_proof`)
+ per-round `SingleRound.reduction_perfectCompleteness`.
-/

open ProtocolSpec OracleComp OracleSpec
open scoped NNReal

namespace Sumcheck.Spec

variable {R : Type} [CommSemiring R] [SampleableType R] {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

-- probe: the per-round leading direction
example : (SingleRound.pSpec R deg).dir ⟨0, by omega⟩ = .P_to_V := by
  decide

end Sumcheck.Spec
