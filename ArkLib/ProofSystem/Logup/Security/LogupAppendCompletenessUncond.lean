/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.LogupCompletenessWired

/-! # LogUp `AppendCompletenessResidual` — unconditional providers (issue #13)

`Logup.AppendCompletenessResidual` (`SubPhaseSplit.lean`) is *indexed* by the two sub-phase
completeness proofs (`hOuter`, `hSumcheck`) that `OracleReduction.append_completeness` consumes.
Every existing provider (`appendCompletenessResidual_wired`, the seam variants) therefore takes
those residuals as **hypothesis binders**, so the residual remains census-open even though the
combined fact `logupCompletenessBrickResidual_holds` (`LogupCompletenessWired.lean`) is a proven,
axiom-clean theorem producing exactly the existential
`∃ hOuter hSumcheck, AppendCompletenessResidual … hOuter hSumcheck`.

This file closes that gap with **direct, unconditional providers** of the named residual itself:

* `appendCompletenessResidual_unconditional` — `AppendCompletenessResidual`, instantiated at the
  in-tree proven sub-phase providers (`outerCompletenessResidual_of_neverFail`,
  `sumcheckCompletenessResidual_unconditional`), from **only** the standard side-condition set
  `{hn, hInit, hImplSupp, himplSP, himplNF, himplVB}` — the same set as the headline
  `logup_completeness_final`, all instantiated by the concrete `ZMod 5` witness in
  `LogupCompletenessFinal.lean`. No census residual appears as a hypothesis.

* `appendCompletenessResidual_forall` — the residual at **arbitrary** proof indices
  `hOuter`/`hSumcheck`, from the same standard side conditions.

There is no weakening and no new mathematics: the underlying Prop
`OracleReduction.appendCompletenessResidual R₁ R₂ h₁ h₂ :=
(R₁.append R₂).completeness init impl rel₁ rel₃ (e₁ + e₂)` does **not** depend on the proof
arguments `h₁`/`h₂` (they index the statement for threading into `append_completeness` but are
unused in the body), so one instance is definitionally every instance. Both theorems conclude the
full named residual; the proof destructures `logupCompletenessBrickResidual_holds` and transports
across that definitional proof-index irrelevance.

The axiom audit at the bottom confirms axiom-cleanliness (`propext`, `Classical.choice`,
`Quot.sound`; no `sorryAx`).
-/

open OracleComp OracleSpec ProtocolSpec

namespace Logup

section AppendUncond

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances when naming the sub-phase obligations. -/
local instance instInhabitedFieldAppendUncond : Inhabited F := ⟨0⟩

/-- **`AppendCompletenessResidual` — unconditional (issue #13).** The non-perfect
outer⊕sumcheck append-composition completeness brick, instantiated at the two in-tree proven
sub-phase providers, from **only** the standard data / honest-implementation side conditions
(the same set as `logup_completeness_final`, all discharged by the concrete `ZMod 5` witness).
No sub-phase residual is consumed as a hypothesis: the proof destructures the proven
`logupCompletenessBrickResidual_holds` and uses that the residual's body does not depend on its
proof indices. -/
theorem appendCompletenessResidual_unconditional
    (hn : 0 < n) (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    AppendCompletenessResidual oSpec F n M params init impl
      (outerCompletenessResidual_of_neverFail oSpec F n M params init impl hInit)
      (sumcheckCompletenessResidual_unconditional oSpec F n M params init impl
        hInit hImplSupp) := by
  obtain ⟨hO, hS, hA⟩ := logupCompletenessBrickResidual_holds oSpec F n M params init impl
    hn hInit hImplSupp himplSP himplNF himplVB
  -- `AppendCompletenessResidual … h₁ h₂` does not depend on `h₁`/`h₂`: definitional transport.
  exact hA

/-- **`AppendCompletenessResidual` at arbitrary proof indices.** The residual's body ignores its
two proof arguments, so the unconditional instance above provides it at *every* pair
`hOuter`/`hSumcheck`. Convenience form for consumers holding their own sub-phase proofs. -/
theorem appendCompletenessResidual_forall
    (hn : 0 < n) (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s'))
    (hOuter : OuterCompletenessResidual oSpec F n M params init impl)
    (hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl) :
    AppendCompletenessResidual oSpec F n M params init impl hOuter hSumcheck :=
  appendCompletenessResidual_unconditional oSpec F n M params init impl
    hn hInit hImplSupp himplSP himplNF himplVB

end AppendUncond

end Logup

/- Axiom audit: must be ⊆ {propext, Classical.choice, Quot.sound} with NO sorryAx. -/
#print axioms Logup.appendCompletenessResidual_unconditional
#print axioms Logup.appendCompletenessResidual_forall
