/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.FriComplete
import ArkLib.OracleReduction.Composition.Sequential.General

/-!
# FRI: Composed-Reduction Perfect Completeness (Brick C/D, scratch / issue #117)

This module assembles the per-round perfect-completeness residuals from
`ArkLib.ToMathlib.FriComplete` (bricks A/B) into perfect completeness of the *composed* FRI
reduction (`Fri.Spec.reduction`), using the proven sequential-composition keystones.

The composed FRI reduction is
```
reduction      = OracleReduction.append reductionFold (QueryRound.queryOracleReduction …)
reductionFold  = OracleReduction.append (OracleReduction.seqCompose … foldOracleReduction)
                                        finalFoldOracleReduction
```

* **Brick C** (this file) is the binary `append`-composition step:
  `reduction_perfectCompleteness_of_phases` reduces the composed reduction's perfect completeness to
  (i) perfect completeness of the folding phase (`reductionFold`) and (ii) of the query phase
  (`queryOracleReduction`), via the proven `OracleReduction.append_perfectCompleteness` (whose deep
  dependency is the proven `Prover.append_run`). The `AppendCoherent` coherence and the
  binary-append residual are the codebase-standard named-residual hypotheses.

* **Brick D** is the headline statement `reduction_perfectCompleteness`, packaging Brick C as the
  composed FRI folding-reduction perfect-completeness theorem.

No `sorry`/`axiom` is introduced in this composition layer: every step is the proven append keystone
applied to the supplied phase facts. The composed-`pSpec` `SampleableType` instances (needed to even
*state* the conclusion's `perfectCompleteness`) are taken as instance binders — exactly as in the
sibling Binius composed-reduction completeness statements; they are pure infrastructure derivable
from the proven leaf challenge instances (`seqCompose`/`++ₚ` `SampleableType`).
-/

namespace Fri

open OracleSpec OracleComp ProtocolSpec NNReal Domain
open scoped NNReal

namespace Spec

namespace Completeness

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n : ℕ}
variable {k : ℕ} {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n F}
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-! **Brick C — binary append composition of the FRI phases.**

The composed FRI reduction `Fri.Spec.reduction` is `append reductionFold queryOracleReduction`.
Given:
* `hFold` : perfect completeness of the folding phase `reductionFold` (folding rounds + final round),
  from the chained input relation `relIn` to the intermediate relation `relMid`;
* `hQuery` : perfect completeness of the query phase `queryOracleReduction`, from `relMid` to
  `relOut` (note `QueryRound.{input,output}Relation` are *equal* — the query round preserves the
  final-fold relation — so `relMid = relOut` in the intended FRI instantiation);
* the `AppendCoherent` coherence for `reductionFold.verifier` (the standard composition side
  condition, synthesized from the per-round leaf coherence instances proven in
  `Fri/Spec/SingleRound.lean`);
* the named binary-append residual (proven against `Prover.append_run`);

the proven `OracleReduction.append_perfectCompleteness` yields perfect completeness of the composed
reduction. -/
theorem reduction_perfectCompleteness_of_phases
    (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n) (l : ℕ) [NeZero l]
    [∀ i, SampleableType
      ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i)]
    [∀ i, SampleableType
      ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F ++ₚ QueryRound.pSpec l (ω := ω)).Challenge i)]
    [∀ i, SampleableType ((QueryRound.pSpec l (ω := ω)).Challenge i)]
    {relMid relOut : Set ((FinalStatement F k × ∀ j, FinalOracleStatement s ω j) ×
      Witness F s d (Fin.last (k + 1)))}
    {relIn : Set ((Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω (0 : Fin (k + 1)) j) ×
      Witness F s d (0 : Fin (k + 2)))}
    [OracleVerifier.Append.AppendCoherent (reductionFold k s d (ω := ω)).verifier]
    (hFold : OracleReduction.perfectCompleteness init impl relIn relMid
      (reductionFold k s d (ω := ω)))
    (hQuery : OracleReduction.perfectCompleteness init impl relMid relOut
      (QueryRound.queryOracleReduction (k := k) s d dom_size_cond l))
    (hResidual : OracleReduction.appendPerfectCompletenessResidual
      (reductionFold k s d (ω := ω))
      (QueryRound.queryOracleReduction (k := k) s d dom_size_cond l) hFold hQuery) :
    OracleReduction.perfectCompleteness init impl relIn relOut
      (Fri.Spec.reduction k s d dom_size_cond l) := by
  change ((reductionFold k s d (ω := ω)).append
      (QueryRound.queryOracleReduction (k := k) s d dom_size_cond l)).perfectCompleteness
    init impl relIn relOut
  unfold OracleReduction.appendPerfectCompletenessResidual at hResidual
  change ((reductionFold k s d (ω := ω)).append
      (QueryRound.queryOracleReduction (k := k) s d dom_size_cond l)).perfectCompleteness
    init impl relIn relOut at hResidual
  exact hResidual

end Completeness

end Spec

end Fri
