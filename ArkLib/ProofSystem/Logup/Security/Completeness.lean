import ArkLib.OracleReduction.Security.Basic
import ArkLib.ProofSystem.Logup.Protocol

/-!
# LogUp Completeness

Main completeness statement for Protocol 2 of `paper.txt`.
-/

open scoped NNReal

namespace Logup

section Completeness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Completeness error forced by the current rejection-based model of the `x` challenge.

Protocol 2 samples `x` from the complement of the table poles. The current verifier samples from
all of `F` and rejects poles, so the intended completeness statement carries this explicit bad-`x`
probability. Once the challenge sampler is modeled as the complement distribution, this should
collapse to perfect completeness.
-/
noncomputable def logupCompletenessError (F : Type) [Fintype F] (n : ℕ) : ℝ≥0 :=
  (Fintype.card (Hypercube n) : ℝ≥0) / (Fintype.card F)

end Completeness

end Logup
