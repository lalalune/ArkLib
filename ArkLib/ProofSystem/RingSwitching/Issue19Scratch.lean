import ArkLib.ProofSystem.RingSwitching.SumcheckPhase

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal
open Sumcheck.Structured

namespace RingSwitching.SumcheckPhase
noncomputable section

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (aOStmtIn : AbstractOStmtIn L ℓ')
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-!
This scratch file used to contain an attempted proof of the iterated sumcheck round
perfect-completeness residual. The actual source module now exposes that obligation as the named
`Prop` `iteratedSumcheckOracleReduction_perfectCompleteness_residual`, so keeping a duplicate
scratch theorem with executable holes made the root sorry census fail without adding a usable API.

The alias below keeps this file as an importable audit anchor while leaving the real proof obligation
explicit and unlaundered in `SumcheckPhase.lean`.
-/

/-- Scratch/audit alias for the live iterated-sumcheck completeness frontier. -/
abbrev iteratedSumcheckOracleReduction_perfectCompleteness_residual_frontier : Prop :=
    iteratedSumcheckOracleReduction_perfectCompleteness_residual
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn) (init := init) (impl := impl)

end
end RingSwitching.SumcheckPhase
