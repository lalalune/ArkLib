import ArkLib.OracleReduction.Security.Basic
import ArkLib.ProofSystem.Logup.Protocol

/-!
# LogUp Soundness

Main soundness statement for Protocol 2 of `paper.txt`.

## Current proof boundary

The theorem below is the paper-shaped end-to-end soundness statement for the composed verifier
`logupVerifier = OracleVerifier.append outerVerifier sumcheckVerifier`. Closing it honestly requires
three facts that are not currently available in-tree:

* an outer LogUp verifier soundness theorem for `outerVerifier`, with intermediate language
  `(midRelation F n M params).language` and error
  `((((M + 1) * Fintype.card (Hypercube n) - 1 : ℕ) : ℝ≥0) /
    ((Fintype.card F - Fintype.card (Hypercube n) : ℕ) : ℝ≥0)) +
    (((params.numGroups + 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0))`;
* a lifted embedded-sumcheck soundness theorem for `sumcheckVerifier`, obtained from generic
  `Sumcheck.Spec.oracleVerifier` soundness and the `logupSumcheckContextLens` /
  `logupSumcheckOracleLens` soundness conditions, with error `sumcheckSoundnessError`;
* the generic sequential-composition probability lemma
  `Verifier.append_soundness` / `OracleVerifier.append_soundness`, whose proof currently reduces to
  a `sorry` in `ArkLib/OracleReduction/Composition/Sequential/Append.lean`.

The generic sumcheck development currently provides single-round completeness and
round-by-round knowledge-soundness infrastructure, but no full plain soundness theorem for
`Sumcheck.Spec.oracleVerifier` at the shape needed here. The final output language is
`Set.univ`, so this theorem is a nontrivial acceptance-probability bound, not a vacuous language
inclusion.
-/

open scoped NNReal

namespace Logup

section Soundness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Paper-shaped soundness error for the LogUp outer checks plus the embedded sumcheck error. -/
noncomputable def logupSoundnessError (F : Type) [Fintype F] (n M : ℕ) (params : ProtocolParams M)
    (sumcheckSoundnessError : ℝ≥0) : ℝ≥0 :=
  ((((M + 1) * Fintype.card (Hypercube n) - 1 : ℕ) : ℝ≥0) /
      ((Fintype.card F - Fintype.card (Hypercube n) : ℕ) : ℝ≥0)) +
    (((params.numGroups + 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)) +
      sumcheckSoundnessError

/-- Main ArkLib soundness theorem for LogUp Protocol 2.

Residual blocker: this is exactly the missing composition of the outer LogUp check soundness, the
lifted embedded-sumcheck soundness, and generic append soundness described in the module docstring.
-/
theorem logup_soundness (sumcheckSoundnessError : ℝ≥0) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) := by
  sorry

end Soundness

end Logup
