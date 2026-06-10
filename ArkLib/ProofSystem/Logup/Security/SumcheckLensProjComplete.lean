/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SumcheckCompletenessClose

/-!
# LogUp Protocol 2 — discharging `SumcheckLensProjComplete` (issue #13, residual RA-projComplete)

This file discharges the named projection hypothesis `hProj` consumed by
`Logup.sumcheckCompletenessResidual_holds`
(in `Security/SumcheckCompletenessClose.lean`):

```
def SumcheckLensProjComplete : Prop :=
  ∀ (stmtIn : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) (witIn : Unit),
    (stmtIn, witIn) ∈ midRelation F n M params →
    ((logupSumcheckContextLens.{0} F n M params).stmt.proj stmtIn,
      (logupSumcheckContextLens.{0} F n M params).wit.proj (stmtIn, witIn))
      ∈ innerSumcheckRelIn F n M params
```

## What the obligation really says

The context lens `logupSumcheckContextLens` projects an outer transcript
`stmtIn = (stmt, oStmt)` to the inner generic-sumcheck input statement
`(logupInitialSumcheckStatement, logupSumcheckOracleStmt stmt oStmt)` and the inner witness `()`
(both `stmt.proj` and `wit.proj` are the *first projections* of the lens's `PFunctor.Lens`
components, evaluated definitionally). Membership in `innerSumcheckRelIn`
(`= Sumcheck.Spec.relationRound … 0`) is, by `unfold`, **exactly** the `Prop`
`Logup.logupSumcheckRelationInput F n M params (Fact.out) stmt oStmt`, i.e. the round-`0`
sum-check claim "`Σ over the sign-hypercube of the LogUp sum-check polynomial = target(=0)`".

With the corrected claim-true `midRelation` (`{p | logupOuterSumcheckClaim … = 0}`, issue #13),
the `(stmtIn, witIn) ∈ midRelation` premise **is** the zero-sum claim, so the obligation closes
unconditionally (`SumcheckLensProjComplete_unconditional` below). The historical conditional forms
(`…_holds` / `…_holds_of_honest`) are retained for callers that thread the claim explicitly. Two
ingredients drive the proof, provided by the in-tree, already-proven bridge:

* **Row-agreement** (`logupSumcheckPolynomialRowsAgree_of_signsDistinct`): the packaged sum-check
  polynomial agrees with `qOnHypercube` on the sign-hypercube. This is *unconditional* given
  `(-1 : F) ≠ 1` (supplied here by the ambient `Fact`), and is discharged inside this file.

* **Zero-sum** (`logupOuterSumcheckClaim … = 0`): the LogUp grand-sum claim vanishes on the
  hypercube. This holds only on the honest-prover support. It is therefore threaded as the explicit
  named hypothesis `hClaimZero` of the main theorem. The companion theorem
  `SumcheckLensProjComplete_holds_of_honest` *discharges* `hClaimZero` on the honest oracles using
  the proven `logupSumcheckRelationInput_of_honest` (which itself rests on
  `honest_helper_sum_zero_of_inputRelation_all` / the grand-sum identity), under the standard
  honest-support side conditions (`inputRelation` membership + table pole-freeness).

The bridge from row-agreement + zero-sum to the `relationRound 0` membership is the proven
`Logup.logupSumcheckRelationInput_of_rowsAgree`.

No `sorry` / `admit`. The only residual sub-hypothesis is `hClaimZero` (the honest zero-sum), and we
additionally show it is discharged on the honest-prover support.
-/

open OracleComp ProtocolSpec

namespace Logup

section SumcheckLensProjComplete

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
variable (n M : ℕ)
variable (params : ProtocolParams M)

local instance : Inhabited F := ⟨0⟩

omit [Fintype F] [DecidableEq F] in
/-- **Key defeq.** The lens projection of an outer transcript `stmtIn = (stmt, oStmt)`, paired with
the projected (trivial) witness, lands in `innerSumcheckRelIn` **iff** the round-`0` LogUp sum-check
input relation `logupSumcheckRelationInput` holds for `stmt`/`oStmt`.

Both `(logupSumcheckContextLens).stmt.proj stmtIn` and `(…).wit.proj (stmtIn, witIn)` are the
*first projections* of the lens's `PFunctor.Lens` fields (`.toFunA`), which by construction are
`fun ctx => (logupInitialSumcheckStatement, logupSumcheckOracleStmt ctx.1 ctx.2)` and `fun _ => ()`
respectively. Hence the membership is definitionally `logupSumcheckRelationInput`. -/
theorem lensProj_mem_innerRel_iff_relationInput
    (stmtIn : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i))
    (witIn : Unit) :
    (((logupSumcheckContextLens.{0} F n M params).stmt.proj stmtIn,
        (logupSumcheckContextLens.{0} F n M params).wit.proj (stmtIn, witIn))
        ∈ innerSumcheckRelIn F n M params)
      ↔
    logupSumcheckRelationInput F n M params (Fact.out : (-1 : F) ≠ 1) stmtIn.1 stmtIn.2 :=
  Iff.rfl

omit [Fintype F] [DecidableEq F] in
/-- **`SumcheckLensProjComplete` holds unconditionally (issue #13, de-larped).**

With the corrected claim-true `midRelation` (`{p | logupOuterSumcheckClaim … = 0}`, matching the
soundness-side `midLanguage`), the `(stmtIn, witIn) ∈ midRelation` premise *is* the zero-sum claim,
so the projection obligation closes by construction: row-agreement is unconditional from
`(-1 : F) ≠ 1` (the ambient `Fact`), and `logupSumcheckRelationInput_of_rowsAgree` bridges
row-agreement + the claim to the round-`0` relation membership. No honest-support hypothesis, no
`hClaimZero` — the `proj_complete` half of the lens completeness is now a theorem. -/
theorem SumcheckLensProjComplete_unconditional :
    SumcheckLensProjComplete F n M params := by
  intro stmtIn _witIn hMid
  -- Reduce the lens-projected membership to the round-`0` input relation (definitional).
  rw [lensProj_mem_innerRel_iff_relationInput F n M params stmtIn _witIn]
  -- `hMid` *is* the zero-sum claim for the corrected `midRelation`; bridge via row-agreement.
  exact logupSumcheckRelationInput_of_rowsAgree
    (F := F) (n := n) (M := M) (params := params)
    (logupSumcheckPolynomialRowsAgree_of_signsDistinct
      (F := F) (n := n) (M := M) (params := params) (Fact.out : (-1 : F) ≠ 1)
      stmtIn.1 stmtIn.2)
    hMid

omit [Fintype F] [DecidableEq F] in
/-- **`SumcheckLensProjComplete` holds, given the honest zero-sum claim.**

The genuine honest content — that the LogUp grand-sum claim vanishes on the hypercube — is taken as
the named hypothesis `hClaimZero` (historical form: with the corrected claim-true `midRelation`
this is subsumed by `SumcheckLensProjComplete_unconditional`). Everything else is proven:
row-agreement is unconditional from `(-1 : F) ≠ 1` (the ambient `Fact`), and the bridge to
`relationRound 0` is `logupSumcheckRelationInput_of_rowsAgree`. -/
theorem SumcheckLensProjComplete_holds
    (hClaimZero :
      ∀ (stmtIn : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)),
        logupOuterSumcheckClaim F n M params stmtIn.1 stmtIn.2 = 0) :
    SumcheckLensProjComplete F n M params := by
  intro stmtIn _witIn _hMid
  -- Reduce the lens-projected membership to the round-`0` input relation (definitional).
  rw [lensProj_mem_innerRel_iff_relationInput F n M params stmtIn _witIn]
  -- Discharge it from unconditional row-agreement + the honest zero-sum claim.
  exact logupSumcheckRelationInput_of_rowsAgree
    (F := F) (n := n) (M := M) (params := params)
    (logupSumcheckPolynomialRowsAgree_of_signsDistinct
      (F := F) (n := n) (M := M) (params := params) (Fact.out : (-1 : F) ≠ 1)
      stmtIn.1 stmtIn.2)
    (hClaimZero stmtIn)

/-- **`SumcheckLensProjComplete` holds on the honest-prover support.**

The honest zero-sum claim `hClaimZero` is *discharged* here from the standard honest-support data:
for every projected outer transcript there is an underlying input `(stmtIn₀, oStmtIn₀)` in
`inputRelation`, the retained oracles are the honest ones built from it, and the verifier's sampled
`xChallenge` avoids all table poles. Under these conditions the zero-sum is the proven
`logupSumcheckRelationInput_of_honest` content (grand-sum identity ⇒ helper-sum `= 0`).

This makes the honest-support restriction explicit: the named hypothesis `hHonest` packages exactly
"the outer phase ran honestly and the pole event did not occur", which is the support on which the
LogUp completeness proof invokes this projection. -/
theorem SumcheckLensProjComplete_holds_of_honest
    (hHonest :
      ∀ (stmtIn : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)),
        ∃ (stmtIn₀ : StmtIn F n M) (oStmtIn₀ : ∀ i, OStmtIn F n M i),
          (((stmtIn₀, oStmtIn₀), ()) ∈ inputRelation F n M) ∧
          (∀ u : Hypercube n,
            stmtIn.1.xChallenge + evalOnHypercube (tableOracle oStmtIn₀) u ≠ 0) ∧
          stmtIn.2 =
            (fun
              | .input i => oStmtIn₀ i
              | .multiplicity => honestMultiplicity oStmtIn₀
              | .helpers => honestHelpers params oStmtIn₀ stmtIn.1.xChallenge)) :
    SumcheckLensProjComplete F n M params := by
  intro stmtIn _witIn _hMid
  rw [lensProj_mem_innerRel_iff_relationInput F n M params stmtIn _witIn]
  obtain ⟨stmtIn₀, oStmtIn₀, hInput, htable, hoStmt⟩ := hHonest stmtIn
  -- Rewrite the projected oracle statements to the honest ones, then invoke the proven honest
  -- round-`0` input relation.
  rw [hoStmt]
  exact logupSumcheckRelationInput_of_honest
    (F := F) (n := n) (M := M) (params := params) (hSigns := (Fact.out : (-1 : F) ≠ 1))
    stmtIn₀ oStmtIn₀ stmtIn.1 hInput htable

/-- **`SumcheckCompletenessResidual` from the inner completeness alone (issue #13, de-larped).**

With `hProj` now a theorem (`SumcheckLensProjComplete_unconditional`, by construction from the
corrected claim-true `midRelation`), the embedded sum-check completeness residual needs only the
inner multi-round oracle sum-check completeness `hInner` — no honest-support hypothesis. -/
theorem sumcheckCompletenessResidual_of_inner
    {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype]
    [SampleableType F]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hInner :
      (logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).perfectCompleteness init impl
        (innerSumcheckRelIn F n M params)
        (innerSumcheckRelOut F n M params)) :
    SumcheckCompletenessResidual oSpec F n M params init impl :=
  sumcheckCompletenessResidual_holds oSpec F n M params init impl
    (SumcheckLensProjComplete_unconditional F n M params) hInner

/-- **Wiring check: the discharged `hProj` plugs into `sumcheckCompletenessResidual_holds`.**

This confirms `SumcheckLensProjComplete_holds_of_honest` has exactly the shape required by the
`hProj` argument of `Logup.sumcheckCompletenessResidual_holds`, so the embedded sum-check phase is
perfectly complete on the honest-prover support given the (separately supplied) inner oracle-level
completeness `hInner` and the honest-support data `hHonest`. -/
theorem sumcheckCompletenessResidual_of_honest
    {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype]
    [SampleableType F]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hHonest :
      ∀ (stmtIn : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)),
        ∃ (stmtIn₀ : StmtIn F n M) (oStmtIn₀ : ∀ i, OStmtIn F n M i),
          (((stmtIn₀, oStmtIn₀), ()) ∈ inputRelation F n M) ∧
          (∀ u : Hypercube n,
            stmtIn.1.xChallenge + evalOnHypercube (tableOracle oStmtIn₀) u ≠ 0) ∧
          stmtIn.2 =
            (fun
              | .input i => oStmtIn₀ i
              | .multiplicity => honestMultiplicity oStmtIn₀
              | .helpers => honestHelpers params oStmtIn₀ stmtIn.1.xChallenge))
    (hInner :
      (logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).perfectCompleteness init impl
        (innerSumcheckRelIn F n M params)
        (innerSumcheckRelOut F n M params)) :
    SumcheckCompletenessResidual oSpec F n M params init impl :=
  sumcheckCompletenessResidual_holds oSpec F n M params init impl
    (SumcheckLensProjComplete_holds_of_honest F n M params hHonest) hInner

end SumcheckLensProjComplete

end Logup

#print axioms Logup.lensProj_mem_innerRel_iff_relationInput
#print axioms Logup.SumcheckLensProjComplete_unconditional
#print axioms Logup.sumcheckCompletenessResidual_of_inner
#print axioms Logup.SumcheckLensProjComplete_holds
#print axioms Logup.SumcheckLensProjComplete_holds_of_honest
#print axioms Logup.sumcheckCompletenessResidual_of_honest
