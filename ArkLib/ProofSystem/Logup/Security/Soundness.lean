import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.ProofSystem.Logup.Protocol

/-!
# LogUp Soundness

Main soundness statement for Protocol 2 of `paper.txt`.

## Proof architecture and the named residual

`logupVerifier` is *definitionally* the sequential composition
`OracleVerifier.append outerVerifier sumcheckVerifier` (see `logupVerifier_eq_append`). Soundness
therefore follows from `OracleVerifier.append_soundness` (the generic sequential-composition
probability lemma, whose `AppendCoherent` side condition for `outerVerifier` is the in-tree
`instOuterVerifierAppendCoherent`), supplying:

* outer-phase soundness for `outerVerifier`, with intermediate language `midLanguage` and error
  `outerSoundnessError` (the two LogUp algebraic-check terms), and
* embedded-sumcheck soundness for `sumcheckVerifier`, with error `sumcheckSoundnessError`.

These two sub-verifier soundness facts are collected into the single named residual
`subPhaseSoundness`, and the top-level `logup_soundness` is reduced to it through
`OracleVerifier.append_soundness` in `logup_soundness_of_residual` (no `sorry`). The error
reconciliation `outerSoundnessError + sumcheckSoundnessError = logupSoundnessError …` holds by
`rfl` because `logupSoundnessError` is *defined* as that sum.

## What blocks `subPhaseSoundness`

Both sub-facts are blocked by missing upstream security lemmas introduced *outside*
`ArkLib/ProofSystem/Logup/**`, which this development is not permitted to modify:

* No outer LogUp verifier soundness theorem for `outerVerifier` exists in-tree (the algebraic
  pole/grand-sum checks of Protocol 2).
* The embedded sumcheck soundness for `sumcheckVerifier` is a `liftContext` of
  `Sumcheck.Spec.oracleVerifier`. The generic sumcheck development currently provides single-round
  completeness and round-by-round knowledge-soundness infrastructure, but no full plain soundness
  theorem for `Sumcheck.Spec.oracleVerifier` at the shape needed here, and the lift also requires
  the `logupSumcheckContextLens` / `logupSumcheckOracleLens` soundness conditions.
* `OracleVerifier.append_soundness` itself reduces to the upstream
  `Verifier.append_soundness` `sorry` (`ArkLib/OracleReduction/Composition/Sequential/Append.lean`).

Hence this single residual `subPhaseSoundness`. The final output language is `Set.univ`
(`outputRelation_language`), so this is a nontrivial acceptance-probability bound, not a vacuous
language inclusion.
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

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances (`instOuterPSpecChallengeSampleable`) used when naming `outerVerifier.soundness`. -/
local instance : Inhabited F := ⟨0⟩

/-- The two LogUp algebraic-check soundness terms for the outer phase: the pole/grand-sum check
error of Protocol 2. This is the `soundnessError₁` summand of `logupSoundnessError`. -/
noncomputable def outerSoundnessError (F : Type) [Fintype F] (n M : ℕ)
    (params : ProtocolParams M) : ℝ≥0 :=
  ((((M + 1) * Fintype.card (Hypercube n) - 1 : ℕ) : ℝ≥0) /
      ((Fintype.card F - Fintype.card (Hypercube n) : ℕ) : ℝ≥0)) +
    (((params.numGroups + 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0))

/-- Paper-shaped soundness error for the LogUp outer checks plus the embedded sumcheck error.

Defined as `outerSoundnessError + sumcheckSoundnessError` so that the
`OracleVerifier.append_soundness` error `soundnessError₁ + soundnessError₂` matches by `rfl`. -/
noncomputable def logupSoundnessError (F : Type) [Fintype F] (n M : ℕ) (params : ProtocolParams M)
    (sumcheckSoundnessError : ℝ≥0) : ℝ≥0 :=
  outerSoundnessError F n M params + sumcheckSoundnessError

/-- The intermediate language threaded between the outer LogUp phase and the embedded sumcheck.
The outer phase carries no acceptance obligation into the sumcheck, so this is `Set.univ` (the
language of the trivial `midRelation` of the completeness development). -/
def midLanguage : Set (StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) :=
  Set.univ

/-- The full LogUp verifier is, definitionally, the sequential composition of the outer verifier and
the embedded sumcheck verifier. This is the structural fact driving the soundness proof via
`OracleVerifier.append_soundness`. -/
theorem logupVerifier_eq_append :
    logupVerifier oSpec F n M params =
      OracleVerifier.append (outerVerifier oSpec F n M params)
        (sumcheckVerifier oSpec F n M params) := rfl

/-- The two sub-phase soundness obligations of the LogUp composition (the smallest named residual).

* The outer phase (`outerVerifier`) is sound with intermediate language `midLanguage` and error
  `outerSoundnessError F n M params`.
* The embedded sumcheck (`sumcheckVerifier`) is sound with error `sumcheckSoundnessError`.

WALL (upstream security/composition gaps, outside `ArkLib/ProofSystem/Logup/**`, not modifiable
here): no in-tree outer LogUp soundness theorem; no full plain `Sumcheck.Spec` soundness theorem at
the lifted shape; and `OracleVerifier.append_soundness` itself reduces to the upstream
`Verifier.append_soundness` sorry. See the module docstring.

Hence this single residual `sorry`. -/
theorem subPhaseSoundness (sumcheckSoundnessError : ℝ≥0) :
    (outerVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language (midLanguage F n M params)
        (outerSoundnessError F n M params) ∧
      (sumcheckVerifier oSpec F n M params).soundness init impl
        (midLanguage F n M params) outputRelation.language sumcheckSoundnessError := by
  sorry

/-- Main ArkLib soundness theorem for LogUp Protocol 2, **reduced to the named residual**
`subPhaseSoundness` through the genuine sequential-composition soundness lemma
`OracleVerifier.append_soundness` (itself upstream-blocked by `sorryAx`; see the module docstring).

The soundness error `logupSoundnessError F n M params s = outerSoundnessError F n M params + s`
is exactly the `soundnessError₁ + soundnessError₂` produced by `append_soundness`. -/
theorem logup_soundness_of_residual (sumcheckSoundnessError : ℝ≥0)
    (h : (outerVerifier oSpec F n M params).soundness init impl
          (inputRelation F n M).language (midLanguage F n M params)
          (outerSoundnessError F n M params) ∧
        (sumcheckVerifier oSpec F n M params).soundness init impl
          (midLanguage F n M params) outputRelation.language sumcheckSoundnessError) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) := by
  obtain ⟨hOuter, hSum⟩ := h
  -- `logupVerifier` is definitionally `append outerVerifier sumcheckVerifier`
  -- (`logupVerifier_eq_append`), and `logupSoundnessError = outerSoundnessError + s`, so the
  -- composed soundness fact unifies with the goal directly.
  exact OracleVerifier.append_soundness.{0, 0}
    (outerVerifier oSpec F n M params) (sumcheckVerifier oSpec F n M params) hOuter hSum

/-- Main ArkLib soundness theorem for LogUp Protocol 2.

Closed via the genuine composition skeleton (`logup_soundness_of_residual`), with the single
residual `subPhaseSoundness`. -/
theorem logup_soundness (sumcheckSoundnessError : ℝ≥0) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  logup_soundness_of_residual oSpec F n M params init impl sumcheckSoundnessError
    (subPhaseSoundness oSpec F n M params init impl sumcheckSoundnessError)

end Soundness

end Logup
