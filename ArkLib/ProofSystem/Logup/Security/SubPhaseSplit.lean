/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.Soundness
import ArkLib.ProofSystem.Logup.Security.Completeness

/-!
# LogUp Protocol 2 — splitting the sub-phase residuals into independent obligations

`Logup.SubPhaseSoundnessResidual` / `Logup.SubPhaseCompletenessResidual`
(in `Security/Soundness.lean` / `Security/Completeness.lean`) each bundle **two**
genuinely-independent sub-verifier obligations into a single conjunction:

* an **outer**-phase obligation (the Protocol-2 pole / grand-sum algebraic checks on
  `outerVerifier` / `outerOracleReduction`), and
* an embedded **sumcheck** obligation (`sumcheckVerifier` / `sumcheckOracleReduction`,
  a `liftContext` of the generic `Sumcheck.Spec` reduction).

The module docstrings of those files explain that the two halves are blocked by
*different* upstream walls (no in-tree outer-LogUp verifier soundness theorem vs. no
plain `Sumcheck.Spec` soundness/completeness theorem + the lens conditions), and that
the outer completeness half is "in principle closable in-tree" while the sumcheck half
is not.

Bundling them as one `Prop` means a future agent who discharges *only* the outer half
(or only the sumcheck half) cannot plug it in. This file therefore **shrinks the
residual surface** (issue #13, acceptance "remove or shrink the residuals") by naming
each half separately and re-deriving the top-level reductions from the split halves:

* `OuterSoundnessResidual` / `SumcheckSoundnessResidual` and the `Iff.rfl` bridge
  `subPhaseSoundnessResidual_iff_split`;
* `logup_soundness_of_split` — `logup_soundness` from the two halves + the append lemma;
* the completeness analogues `OuterCompletenessResidual` / `SumcheckCompletenessResidual`,
  `subPhaseCompletenessResidual_iff_split`, `logup_completeness_of_split`.

No new mathematics and no new axioms: the bridges are definitional and the reductions
chain the existing `logup_soundness_of_residual` / `logup_completeness_of_residual`.
The point is to make the two walls **independently dischargeable** so they can be ground
brick-by-brick.
-/

open scoped NNReal

namespace Logup

section Split

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge
`SampleableType` instances used when naming the outer sub-verifier obligations. -/
local instance : Inhabited F := ⟨0⟩

/-! ### Soundness halves -/

/-- The **outer** half of `SubPhaseSoundnessResidual`: `outerVerifier` is sound from the
input language into `midLanguage` with the LogUp algebraic-check error
`outerSoundnessError`. The first conjunct of `SubPhaseSoundnessResidual`. -/
def OuterSoundnessResidual : Prop :=
  (outerVerifier oSpec F n M params).soundness init impl
    (inputRelation F n M).language (midLanguage F n M params)
    (outerSoundnessError F n M params)

/-- The **sumcheck** half of `SubPhaseSoundnessResidual`: `sumcheckVerifier` is sound from
`midLanguage` into the output language with error `sumcheckSoundnessError`. The second
conjunct of `SubPhaseSoundnessResidual`. -/
def SumcheckSoundnessResidual (sumcheckSoundnessError : ℝ≥0) : Prop :=
  (sumcheckVerifier oSpec F n M params).soundness init impl
    (midLanguage F n M params) outputRelation.language sumcheckSoundnessError

/-- `SubPhaseSoundnessResidual` is **definitionally** the conjunction of its two halves. -/
theorem subPhaseSoundnessResidual_iff_split (sumcheckSoundnessError : ℝ≥0) :
    SubPhaseSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError ↔
      OuterSoundnessResidual oSpec F n M params init impl ∧
        SumcheckSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError :=
  Iff.rfl

/-- **LogUp soundness from the two independent halves.** Identical conclusion to
`logup_soundness_of_residual`, but consuming the outer and sumcheck soundness obligations
*separately*, so either can be discharged on its own. -/
theorem logup_soundness_of_split (sumcheckSoundnessError : ℝ≥0)
    (hOuter : OuterSoundnessResidual oSpec F n M params init impl)
    (hSumcheck : SumcheckSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError)
    (hAppendSoundness :
      (logupVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language outputRelation.language
        (logupSoundnessError F n M params sumcheckSoundnessError)) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  logup_soundness_of_residual oSpec F n M params init impl sumcheckSoundnessError
    ⟨hOuter, hSumcheck⟩ hAppendSoundness

/-! ### Completeness halves -/

/-- The **outer** half of `SubPhaseCompletenessResidual`: the outer phase is complete with
the pole-rejection error `logupCompletenessError`. The first conjunct of
`SubPhaseCompletenessResidual`; per the `Completeness.lean` docstring this is the
in-principle in-tree-closable half (its failure event is the proven `probEvent_pole_le`). -/
def OuterCompletenessResidual : Prop :=
  (outerOracleReduction oSpec F n M params).completeness init impl
    (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n)

/-- The **sumcheck** half of `SubPhaseCompletenessResidual`: the embedded sumcheck is
complete with error `0`. The second conjunct of `SubPhaseCompletenessResidual`. -/
def SumcheckCompletenessResidual : Prop :=
  (sumcheckOracleReduction oSpec F n M params).completeness init impl
    (midRelation F n M params) outputRelation 0

/-- `SubPhaseCompletenessResidual` is **definitionally** the conjunction of its two halves. -/
theorem subPhaseCompletenessResidual_iff_split :
    SubPhaseCompletenessResidual oSpec F n M params init impl ↔
      OuterCompletenessResidual oSpec F n M params init impl ∧
        SumcheckCompletenessResidual oSpec F n M params init impl :=
  Iff.rfl

/-- **LogUp completeness from the two independent halves.** Identical conclusion to
`logup_completeness_of_residual`, but consuming the outer and sumcheck completeness
obligations *separately*, so either can be discharged on its own. The
`hAppendCompleteness` sequential-composition residual is threaded unchanged (the current
`OracleReduction.append_completeness` carries it as an explicit hypothesis). -/
theorem logup_completeness_of_split
    (hOuter : OuterCompletenessResidual oSpec F n M params init impl)
    (hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl)
    (hAppendCompleteness :
      (logupOracleReduction oSpec F n M params).completeness init impl
        (inputRelation F n M) outputRelation (logupCompletenessError F n)) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_of_residual oSpec F n M params init impl ⟨hOuter, hSumcheck⟩
    hAppendCompleteness

end Split

end Logup
