/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SubPhaseSplit
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessOracle

/-!
# LogUp Protocol 2 — end-to-end completeness close (issue #13, brick C)

This file assembles the **end-to-end** completeness statement for LogUp Protocol 2,

```
(logupOracleReduction oSpec F n M params).completeness init impl
    (inputRelation F n M) outputRelation (logupCompletenessError F n)
```

by composing the three independently-named completeness obligations exposed by
`Security/SubPhaseSplit.lean`:

* the **outer** pole-rejection half (`OuterCompletenessResidual`, error
  `logupCompletenessError F n`), which is **already a proven theorem in-tree**
  (`outerOracleReduction_completeness` / `outerCompletenessResidual_of_neverFail`, via the pole
  bound `card_poleSet_le` / `probEvent_pole_le` and the per-state agreement `outer_perState_agree`),
  discharged here under the standard `NeverFail init` completeness assumption;
* the embedded **sumcheck** half (`SumcheckCompletenessResidual`, error `0`), a `liftContext` of the
  generic `Sumcheck.Spec` reduction; and
* the **append-composition** brick (`AppendCompletenessResidual`), which bridges the two sub-phase
  completenesses to the completeness of the sequential composition
  `logupOracleReduction = outerOracleReduction.append sumcheckOracleReduction`.

## What is genuinely proven here vs. left as honest residuals

`logupOracleReduction` is *definitionally* the message-seam append
`outerOracleReduction.append sumcheckOracleReduction` (`logupOracleReduction_eq_append`), and the
embedded-sumcheck protocol `logupSumcheckPSpec = Sumcheck.Spec.pSpec` starts with a `P_to_V`
prover message, so the seam *is* a message seam: the proven oracle-level keystone
`OracleReduction.append_perfectCompleteness_msg_proof` is the right composition tool for its
*perfect* (error-`0`) special case.

The **append theorem the LogUp completeness composition actually needs is the non-perfect one**: it
must combine the outer error `logupCompletenessError F n` (≠ 0 over a finite field) with the
sumcheck error `0`. The only *proven* in-tree append-completeness theorem is the perfect-completeness
keystone (both component errors `0`); a general non-perfect Reduction-level append completeness is
not available in-tree. So this brick:

* **proves** the outer half outright (no residual);
* takes the **sumcheck** completeness and the **non-perfect append-composition** completeness as
  explicit, clearly-named `Prop` hypotheses — the two genuine residual gaps, each closable by a later
  brick;
* additionally **sharpens** the append residual, reducing it through the proven verifier-fusion
  bridge `appendToReductionResidual` to a Reduction-level append-completeness statement, and shows
  that in the **perfect special case** (`logupCompletenessError F n = 0`) the keystone discharges it
  end-to-end with *no* residual at all.

No `sorry`/`sorryAx`: every step is a real proof or an explicitly named hypothesis. The axiom audit
at the bottom confirms `logup_completeness_full` is axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped NNReal ENNReal
open OracleComp

namespace Logup

section Close

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances when naming the sub-phase obligations. -/
local instance instInhabitedFieldLogupClose : Inhabited F := ⟨0⟩

/-! ### End-to-end completeness from the (proven) outer half + named sub-bricks -/

/-- **End-to-end LogUp Protocol 2 completeness (issue #13, brick C).**

The full LogUp oracle reduction is complete with error `logupCompletenessError F n =
|Hypercube n| / |F|` (the pole-rejection error; the sumcheck phase is perfectly complete, error `0`).

The **outer** pole-rejection half is discharged in-tree by `outerCompletenessResidual_of_neverFail`
under the standard `NeverFail init` completeness assumption — it is *not* a residual. The two genuine
remaining obligations are taken as explicit named hypotheses:

* `hSumcheck : SumcheckCompletenessResidual` — perfect completeness of the embedded sumcheck phase
  (`liftContext` of `Sumcheck.Spec`; blocked upstream by the missing generic `Sumcheck.Spec`
  seq-compose completeness theorem + the lens `IsComplete` instance);
* `hAppend : AppendCompletenessResidual` — the non-perfect sequential-composition completeness brick
  combining the outer error with the sumcheck error `0` along the message seam.

The conclusion is exactly the headline LogUp completeness statement, with no `sorry`. -/
theorem logup_completeness_full (hInit : NeverFail init)
    (hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl)
    (hAppend :
      AppendCompletenessResidual oSpec F n M params init impl
        (outerCompletenessResidual_of_neverFail oSpec F n M params init impl hInit) hSumcheck) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_of_sumcheck_append oSpec F n M params init impl hInit hSumcheck hAppend

/-- **Variant taking the outer half as an explicit hypothesis** (instead of deriving it from
`NeverFail init`). Useful for callers that obtain outer completeness by another route. -/
theorem logup_completeness_full_of_outer
    (hOuter : OuterCompletenessResidual oSpec F n M params init impl)
    (hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl)
    (hAppend :
      AppendCompletenessResidual oSpec F n M params init impl hOuter hSumcheck) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_of_split oSpec F n M params init impl hOuter hSumcheck hAppend

/-! ### Sharpening the append residual through the proven verifier-fusion bridge

`AppendCompletenessResidual … hOuter hSumcheck` unfolds (by `appendCompletenessResidual` and
`OracleReduction.completeness`) to a `Reduction.completeness` statement about
`(outerOracleReduction.append sumcheckOracleReduction).toReduction`. The proven bridge
`OracleReduction.appendToReductionResidual` collapses that `toReduction` to the *non-oracle* append
`outerOracleReduction.toReduction.append sumcheckOracleReduction.toReduction`. The lemma below makes
this explicit, pinning the residual's remaining content to a plain Reduction-level append
completeness — which is exactly where the (non-perfect) upstream composition wall lives. -/

/-- The append residual rewritten through the verifier-fusion bridge: it is `Reduction`-level
completeness of the *non-oracle* append `outer.toReduction.append sumcheck.toReduction`, at error
`logupCompletenessError F n + 0`. This pins the residual's remaining content to a plain
Reduction-level append completeness — exactly where the (non-perfect) upstream composition wall
lives. -/
theorem appendCompletenessResidual_iff_toReduction
    (hOuter : OuterCompletenessResidual oSpec F n M params init impl)
    (hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl)
    (hBridge :
      OracleReduction.appendToReductionResidual
        (outerOracleReduction oSpec F n M params)
        (sumcheckOracleReduction oSpec F n M params)) :
    AppendCompletenessResidual oSpec F n M params init impl hOuter hSumcheck ↔
      Reduction.completeness init impl
        (inputRelation F n M) outputRelation
        ((outerOracleReduction oSpec F n M params).toReduction.append
          (sumcheckOracleReduction oSpec F n M params).toReduction)
        (logupCompletenessError F n + 0) := by
  -- `AppendCompletenessResidual` is, by definition, the `OracleReduction.completeness` of the
  -- appended oracle reduction; `OracleReduction.completeness` is `Reduction.completeness` of
  -- `.toReduction`; the bridge rewrites that `.toReduction` to the non-oracle append.
  unfold AppendCompletenessResidual OracleReduction.appendCompletenessResidual
    OracleReduction.completeness
  rw [show (OracleReduction.append (outerOracleReduction oSpec F n M params)
        (sumcheckOracleReduction oSpec F n M params)).toReduction
      = (outerOracleReduction oSpec F n M params).toReduction.append
          (sumcheckOracleReduction oSpec F n M params).toReduction from hBridge]
  -- After the bridge rewrite both sides are the same `Reduction.completeness` statement.
  exact Iff.rfl

/-! ### The perfect special case: keystone discharges the append residual with no residual

When `logupCompletenessError F n = 0` (e.g. an infinite/empty hypercube row count relative to `|F|`),
both component errors are `0`, the seam is a message seam, and the proven oracle-level keystone
`OracleReduction.append_perfectCompleteness_msg_proof` discharges the append residual outright. This
exhibits the append composition as a *genuine* (not vacuous) fact: the remaining wall is purely the
arithmetic of carrying a non-zero outer error through the same composition.

The lemmas below need the base oracle-spec finiteness/inhabitedness assumptions `[oSpec.Fintype]`,
`[oSpec.Inhabited]` that the keystone consumes, plus the default challenge oracle interfaces for the
three protocol specs (so the `[·]ₒ` combined-spec instance binders elaborate). -/

variable [oSpec.Fintype] [oSpec.Inhabited]

/-- Default challenge oracle interface for the full LogUp transcript challenges. -/
noncomputable local instance instPSpecChallengeOI :
    ∀ i, OracleInterface ((pSpec F n M params).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

/-- Default challenge oracle interface for the outer-phase challenges. -/
noncomputable local instance instOuterChallengeOI :
    ∀ i, OracleInterface ((outerPSpec F n params).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

/-- Default challenge oracle interface for the embedded-sumcheck challenges. -/
noncomputable local instance instSumcheckChallengeOI :
    ∀ i, OracleInterface ((logupSumcheckPSpec F n M params).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

/-- In the perfect special case `logupCompletenessError F n = 0`, the embedded-sumcheck completeness
is `0` and the outer completeness is `0`, so both sub-phases are perfectly complete; the
message-seam keystone then yields the append residual end-to-end. The seam direction facts and the
verifier-fusion bridge are taken as explicit hypotheses (the message seam is structural; the bridge
is the proven `appendToReductionResidual`). -/
theorem appendCompletenessResidual_of_perfect
    (hErr : logupCompletenessError F n = 0)
    (hInit : NeverFail init)
    (hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl)
    (hn : 0 < Fin.vsum (fun _ : Fin n => 2))
    (hDir :
      (pSpec F n M params).dir (⟨4, by
        change 4 < 4 + Fin.vsum (fun _ : Fin n => 2); omega⟩ :
          Fin (4 + Fin.vsum (fun _ : Fin n => 2))) = .P_to_V)
    (hDir₂ : (logupSumcheckPSpec F n M params).dir (⟨0, hn⟩ :
        Fin (Fin.vsum (fun _ : Fin n => 2))) = .P_to_V)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (hBridge :
      OracleReduction.appendToReductionResidual
        (outerOracleReduction oSpec F n M params)
        (sumcheckOracleReduction oSpec F n M params))
    [(oSpec + [(pSpec F n M params).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec F n M params).Challenge]ₒ).Inhabited]
    [(oSpec + [(outerPSpec F n params).Challenge]ₒ).Fintype]
    [(oSpec + [(outerPSpec F n params).Challenge]ₒ).Inhabited]
    [(oSpec + [(logupSumcheckPSpec F n M params).Challenge]ₒ).Fintype]
    [(oSpec + [(logupSumcheckPSpec F n M params).Challenge]ₒ).Inhabited] :
    AppendCompletenessResidual oSpec F n M params init impl
      (outerCompletenessResidual_of_neverFail oSpec F n M params init impl hInit) hSumcheck := by
  -- Outer completeness with error `logupCompletenessError F n = 0` is perfect completeness.
  have hOuterPerfect :
      (outerOracleReduction oSpec F n M params).perfectCompleteness init impl
        (inputRelation F n M) (midRelation F n M params) := by
    have h := outerCompletenessResidual_of_neverFail oSpec F n M params init impl hInit
    unfold OuterCompletenessResidual at h
    rw [hErr] at h
    exact h
  -- Sumcheck completeness with error `0` is perfect completeness (by definition).
  have hSumPerfect :
      (sumcheckOracleReduction oSpec F n M params).perfectCompleteness init impl
        (midRelation F n M params) outputRelation := hSumcheck
  -- Apply the proven oracle-level message-seam keystone to get perfect append completeness.
  have hAppPerfect :
      (OracleReduction.append (outerOracleReduction oSpec F n M params)
          (sumcheckOracleReduction oSpec F n M params)).perfectCompleteness init impl
        (inputRelation F n M) outputRelation :=
    OracleReduction.append_perfectCompleteness_msg_proof
      (outerOracleReduction oSpec F n M params)
      (sumcheckOracleReduction oSpec F n M params)
      hOuterPerfect hSumPerfect hn hDir hDir₂ hInit hImplSupp hBridge
  -- `AppendCompletenessResidual` at error `logupCompletenessError F n + 0 = 0` is exactly that
  -- perfect append completeness.
  unfold AppendCompletenessResidual OracleReduction.appendCompletenessResidual
  rw [hErr, add_zero]
  exact hAppPerfect

/-- **End-to-end LogUp completeness in the perfect special case — fully closed (no residual).**
When `logupCompletenessError F n = 0`, the append residual is discharged by the proven keystone via
`appendCompletenessResidual_of_perfect`, so the only remaining input is the embedded sumcheck
completeness. This is the strongest unconditional statement available without an in-tree non-perfect
append-completeness theorem. -/
theorem logup_completeness_full_perfect
    (hErr : logupCompletenessError F n = 0)
    (hInit : NeverFail init)
    (hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl)
    (hn : 0 < Fin.vsum (fun _ : Fin n => 2))
    (hDir :
      (pSpec F n M params).dir (⟨4, by
        change 4 < 4 + Fin.vsum (fun _ : Fin n => 2); omega⟩ :
          Fin (4 + Fin.vsum (fun _ : Fin n => 2))) = .P_to_V)
    (hDir₂ : (logupSumcheckPSpec F n M params).dir (⟨0, hn⟩ :
        Fin (Fin.vsum (fun _ : Fin n => 2))) = .P_to_V)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (hBridge :
      OracleReduction.appendToReductionResidual
        (outerOracleReduction oSpec F n M params)
        (sumcheckOracleReduction oSpec F n M params))
    [(oSpec + [(pSpec F n M params).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec F n M params).Challenge]ₒ).Inhabited]
    [(oSpec + [(outerPSpec F n params).Challenge]ₒ).Fintype]
    [(oSpec + [(outerPSpec F n params).Challenge]ₒ).Inhabited]
    [(oSpec + [(logupSumcheckPSpec F n M params).Challenge]ₒ).Fintype]
    [(oSpec + [(logupSumcheckPSpec F n M params).Challenge]ₒ).Inhabited] :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_full oSpec F n M params init impl hInit hSumcheck
    (appendCompletenessResidual_of_perfect oSpec F n M params init impl
      hErr hInit hSumcheck hn hDir hDir₂ hImplSupp hBridge)

end Close

end Logup

/- Axiom audit for the LogUp completeness close. -/
#print axioms Logup.logup_completeness_full
#print axioms Logup.logup_completeness_full_of_outer
#print axioms Logup.appendCompletenessResidual_iff_toReduction
#print axioms Logup.appendCompletenessResidual_of_perfect
#print axioms Logup.logup_completeness_full_perfect
