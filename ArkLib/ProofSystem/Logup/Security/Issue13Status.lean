/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.LogupSoundnessUncond

/-!
# LogUp Protocol 2 — issue #13 final status (single documentation entry point)

This file is the **single entry point** documenting exactly what issue #13 (LogUp Protocol 2,
completeness + soundness) has been reduced to after the binary verifier-fusion keystone
`OracleReduction.oracleVerifier_append_toVerifier`
(`Composition/Sequential/AppendToVerifierKeystone.lean`, **proven sorry-free**) discharged the deep
append-composition oracle routing on both the completeness and soundness sides.

It re-exports the two headline statements under stable `issue13_*` names, alongside the axiom audit.

## Why this file imports only the soundness cone

The two most-unconditional assemblies live in
`Security/LogupCompletenessUncond.lean` (`logup_completeness_uncond`, residual surface
`{hInit, hHonest, hPerRound, hImplSupp, hAppend}`) and
`Security/LogupSoundnessUncond.lean` (`logup_soundness_uncond`, residual surface
`{hOuter, hSumcheck, hPlainAppend}`). They **cannot be co-imported**: the completeness cone pulls in
`Security/SumcheckCompletenessClose.lean` and the soundness cone pulls in
`Security/LogupSoundnessClose.lean`, and *both* of those files declare an anonymous
`local instance : Inhabited F := ⟨0⟩` that Lean auto-names identically
(`Logup.instInhabited_arkLib_2`, the second anonymous `Logup` instance in each module). Merging both
environments at import time fails with
`environment already contains 'Logup.instInhabited_arkLib_2'`. Those files may not be edited, and the
clash is an *environment merge* event that occurs before any of this file's code runs, so neither a
local `attribute` shadow nor a renamed local instance can prevent it.

Resolution (per the issue #13 plan): anchor on the **soundness** cone — it is the one carrying the
defs (`midSoundnessProtocolLanguage`, `logup_soundness_full`) that cannot be relocated outside the
clashing module — and reach the **completeness** headline through the clash-free base
`Security/Completeness.lean` (`logup_completeness_of_residual`, residual surface
`SubPhaseCompletenessResidual` + the append-completeness residual), which is transitively imported
here. The finer 5-hypothesis completeness residual `logup_completeness_uncond` remains available as a
sibling entry point in `LogupCompletenessUncond.lean`; it is referenced below in prose, not imported.

## The two headlines (issue #13)

* `Logup.issue13_soundness` — the headline LogUp Protocol 2 soundness, reduced to the **minimal**
  named residual set `{hOuter, hSumcheck, hPlainAppend}` (a straight re-export of
  `logup_soundness_uncond`). The deep oracle routing of the append seam has been discharged by the
  proven binary fusion; what remains is the corrected outer Schwartz–Zippel half over the
  non-degenerate `midSoundnessProtocolLanguage`, the embedded-sumcheck `liftContext` half over the
  same language, and the plain-verifier malicious-prover seam union bound.

* `Logup.issue13_completeness` — the headline LogUp Protocol 2 completeness, reduced to the named
  residual `SubPhaseCompletenessResidual` (the two sub-phase completeness facts: outer pole rejection
  with error `logupCompletenessError F n`, and the perfect embedded-sumcheck phase) plus the
  append-completeness residual (a re-export of `logup_completeness_of_residual`). The *finer*
  five-hypothesis surface `{hInit, hHonest, hPerRound, hImplSupp, hAppend}` is what
  `Logup.logup_completeness_uncond` (sibling file `LogupCompletenessUncond.lean`) further reduces
  these to; that cone is un-coimportable here for the reason above.

## Final residual surface of issue #13

Soundness: `{hOuter, hSumcheck, hPlainAppend}` (3 named hypotheses).
Completeness: `{SubPhaseCompletenessResidual, appendCompletenessResidual}`, themselves further
reduced by the sibling `logup_completeness_uncond` to
`{hInit, hHonest, hPerRound, hImplSupp, hAppend}` (5 named hypotheses).

No `sorry`/`sorryAx`/`admit`: every step is a real proof or an explicitly named hypothesis. The axiom
audit at the bottom confirms axiom-cleanliness (`propext`, `Classical.choice`, `Quot.sound`).
-/

open scoped NNReal ENNReal
open OracleComp OracleSpec ProtocolSpec

namespace Logup

section Issue13

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances (`instOuterPSpecChallengeSampleable`) used when stating `outerVerifier.soundness` and
the outer/sumcheck completeness obligations — matching the local instances used throughout the
LogUp security development. -/
local instance instInhabitedFieldIssue13 : Inhabited F := ⟨0⟩

/-! ### Issue #13 soundness — minimal residual `{hOuter, hSumcheck, hPlainAppend}` -/

/-- **Issue #13 — LogUp Protocol 2 soundness (final status).**

The full LogUp verifier is sound from the input language into the (trivial) output language
`Set.univ` with the paper-shaped error
`logupSoundnessError F n M params sumcheckSoundnessError =
outerSoundnessError F n M params + sumcheckSoundnessError`. Everything mechanical — the definitional
`logupVerifier = OracleVerifier.append outerVerifier sumcheckVerifier`, the error reconciliation, the
`append_soundness` chaining, and crucially the **oracle routing of the append seam** (discharged by
the proven binary verifier fusion `oracleVerifier_append_toVerifier`) — is closed. The smallest
honest residual set:

* `hOuter` — the corrected protocol-level outer soundness over the non-degenerate
  `midSoundnessProtocolLanguage` (Schwartz–Zippel mathematics proven in `OuterSoundnessReal.lean`,
  run-marginal isolated to the proven `OuterRunMarginalToUniform`);
* `hSumcheck` — the embedded-sumcheck soundness over `midSoundnessProtocolLanguage` (the
  `liftContext` of generic sum-check soundness; `sumcheckSoundnessResidual_holds` supplies the
  `midLanguage` analogue);
* `hPlainAppend` — the **plain-verifier** append-soundness residual (malicious-prover seam
  decomposition + union bound, oracle routing already discharged).

This is a straight re-export of `logup_soundness_uncond`. -/
theorem issue13_soundness (sumcheckSoundnessError : ℝ≥0)
    (hOuter :
      (outerVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language (midSoundnessProtocolLanguage F n M params)
        (outerSoundnessError F n M params))
    (hSumcheck :
      (sumcheckVerifier oSpec F n M params).soundness init impl
        (midSoundnessProtocolLanguage F n M params) outputRelation.language
        sumcheckSoundnessError)
    (hPlainAppend :
      (Verifier.append (outerVerifier oSpec F n M params).toVerifier
          (sumcheckVerifier oSpec F n M params).toVerifier).soundness init impl
        (inputRelation F n M).language outputRelation.language
        (outerSoundnessError F n M params + sumcheckSoundnessError)) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  logup_soundness_uncond oSpec F n M params init impl sumcheckSoundnessError
    hOuter hSumcheck hPlainAppend

/-- **Issue #13 — bundled-residual front door for soundness.**

Packages the three remaining soundness obligations into one existential `Prop` and re-derives the
headline. A re-export of `logup_soundness_uncond_of_residual`. -/
theorem issue13_soundness_of_residual (sumcheckSoundnessError : ℝ≥0)
    (h : LogupSoundnessUncondResidual oSpec F n M params init impl sumcheckSoundnessError) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  logup_soundness_uncond_of_residual oSpec F n M params init impl sumcheckSoundnessError h

/-! ### Issue #13 completeness — residual `SubPhaseCompletenessResidual` + append residual

The finer five-hypothesis surface `{hInit, hHonest, hPerRound, hImplSupp, hAppend}` is delivered by
the sibling `Logup.logup_completeness_uncond` (`LogupCompletenessUncond.lean`), which is the
un-coimportable cone documented at the top of this file. Here we re-export the clash-free
`logup_completeness_of_residual`, whose residual `SubPhaseCompletenessResidual` is *exactly* the two
sub-phase completeness facts that the sibling cone further reduces. -/

/-- **Issue #13 — LogUp Protocol 2 completeness (final status).**

The full LogUp oracle reduction is complete with error `logupCompletenessError F n` (`= |Hypercube n|
/ |F|`, the outer pole-rejection error plus the perfect sumcheck error `0`), reduced through the
genuine sequential-composition completeness interface `OracleReduction.append_completeness`. The
remaining obligations:

* `h : SubPhaseCompletenessResidual …` — the two sub-phase completeness facts: the outer phase is
  complete with error `logupCompletenessError F n`, and the embedded sumcheck phase is *perfectly*
  complete. The sibling cone `logup_completeness_uncond` further reduces these to the five named
  hypotheses `{hInit, hHonest, hPerRound, hImplSupp, hAppend}`, with the deep unbounded-round verifier
  fusion already discharged by the proven binary keystone.
* `hAppendCompleteness : … .appendCompletenessResidual …` — the sequential-composition completeness
  fact carried as the explicit residual hypothesis by the `append_completeness` API.

This is a straight re-export of `logup_completeness_of_residual`. -/
theorem issue13_completeness
    (h : SubPhaseCompletenessResidual oSpec F n M params init impl)
    (hAppendCompleteness :
      (outerOracleReduction oSpec F n M params).appendCompletenessResidual
        (sumcheckOracleReduction oSpec F n M params) h.1 h.2) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_of_residual oSpec F n M params init impl h hAppendCompleteness

end Issue13

end Logup

/- Axiom audit for the issue #13 final-status entry points. -/
#print axioms Logup.issue13_soundness
#print axioms Logup.issue13_soundness_of_residual
#print axioms Logup.issue13_completeness
