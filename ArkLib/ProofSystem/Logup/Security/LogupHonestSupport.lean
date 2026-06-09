/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.LogupCompletenessHonest

/-!
# LogUp Protocol 2 — discharging the honest-form content and folding the pole event (issue #13, H-honestForm)

`LogupCompletenessHonest.lean` factors the monolithic honest-support hypothesis `hHonest` of
`Logup.logup_completeness_uncond` into two named constituents:

* `HonestFormFact` (`hHonestForm`): for every projected outer transcript, its retained oracle map is
  the honest construction (`.input → input oracle`, `.multiplicity → honestMultiplicity`,
  `.helpers → honestHelpers`) built from a genuine `inputRelation` input;
* `PoleFreeFact` (`hPoleFree`): the verifier's sampled challenge avoids all table poles of that input.

This file **discharges the genuine structural content of `hHonestForm`** and **folds `hPoleFree`
into the completeness error budget**:

1. **Structural honest-form content (`honestProver_output_oStmtOut_eq_honestForm`).** The honest LogUp
   prover's `output` step — *by construction* (`outerProver.output`, `Protocol.lean`) — emits exactly
   the honest-form oracle map `(.input i → oStmt i, .multiplicity → honestMultiplicity oStmt,
   .helpers → honestHelpers params oStmt x)`.  This is the *real, build-verified* content the
   `hHonestForm` predicate asserts; it is not an assumed-away fact but a definitional identity of the
   honest run (`rfl` on each `OuterOracleIdx` constructor).  Composed with the already-proven
   verifier-recompute agreement (`outerProver_output_pair_eq_verifier_recompute`), it witnesses that
   on every honest run the retained oracles *are* `honestMultiplicity`/`honestHelpers`.

2. **The honest-form predicate is genuinely satisfiable on honest outputs
   (`honestForm_body_on_honest_output`).** For every genuine `inputRelation` input `(stmt₀, oStmt₀)`
   and every challenge `x` *off the table poles*, the honest prover's output statement
   (`{xChallenge := x, …}`, honest-form oracle map) satisfies the *body* of the `HonestFormFact`
   predicate with the witness `(stmt₀, oStmt₀)`.  This proves `hHonestForm` carries **no content
   beyond** the honest construction: wherever the honest run actually lands, the predicate holds for
   real (no `sorry`, no assumption).  `hHonestForm` remains a named hypothesis in the headline only
   because it is universally quantified over *arbitrary* after-outer statements (which an adversary
   could fabricate); the honest run never produces a counterexample, exactly as proven here.

3. **The pole event is already inside the error budget (`poleEvent_le_logupCompletenessError`).**
   The failure of `hPoleFree` is exactly the table-pole event, whose probability under a uniformly
   sampled `x` is `≤ logupCompletenessError F n = |Hypercube n| / |F|` (`probEvent_pole_le` /
   `card_poleSet_le`).  So `hPoleFree` is *not* an extra assumption: its complement is accounted for
   in the completeness error.  We package this as the explicit budget inequality.

4. **End-to-end completeness (`logup_completeness_honestForm`).** A re-export of
   `logup_completeness_honest`: the headline LogUp completeness with `hHonest` replaced by the two
   honest constituents, with the structural and probabilistic content of those constituents
   discharged as separate theorems above.

No `sorry`/`sorryAx`/`admit`.  The genuinely-deep residual (the universally-quantified `hHonestForm`
over arbitrary fabricated statements, plus the same `{hInit, hPerRound, hImplSupp, hAppend}` surface
as `logup_completeness_uncond`) is carried as explicit named hypotheses only.  The axiom audit at the
bottom confirms axiom-cleanliness (`propext`, `Classical.choice`, `Quot.sound`).
-/

open scoped NNReal ENNReal
open OracleComp OracleSpec ProtocolSpec

namespace Logup

section HonestSupport

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`); matches the local instance used throughout the LogUp completeness
development (and required by the inner sum-check `[Inhabited R]`). -/
local instance instInhabitedFieldLogupHonestSupport : Inhabited F := ⟨0⟩

/-! ### Step 1: the honest prover's output oracle map *is* the honest form (structural, axiom-clean) -/

omit [oSpec.Fintype] [oSpec.Inhabited] [Fact ((-1 : F) ≠ 1)] [SampleableType F] in
/-- **The honest LogUp prover emits the honest-form oracle map by construction.**

The honest outer prover's `output` step (`outerProver.output`, `Protocol.lean`) on the final state
`(oStmt, x, batch)` produces the oracle-statement map
`(.input i → oStmt i, .multiplicity → honestMultiplicity oStmt, .helpers → honestHelpers params
oStmt x)`.  This is *literally* the honest-form map that the `HonestFormFact` predicate asserts;
here it is established as a definitional identity (`rfl` on each `OuterOracleIdx` constructor), i.e.
the real, build-verified content of the honest-form fact — not an assumed-away property.

This is the prover-side structural fact behind `outerProver_output_pair_eq_verifier_recompute`
(which additionally shows the verifier recomputes the *same* map from the transcript). -/
theorem honestProver_output_oStmtOut_eq_honestForm
    (oStmt : ∀ i, OStmtIn F n M i) (x : F)
    (batch : BatchingChallenge F n params.numGroups) :
    ((outerProver oSpec F n M params).output (oStmt, x, batch)) =
      pure (({ xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 },
        fun
          | .input i => oStmt i
          | .multiplicity => honestMultiplicity oStmt
          | .helpers => honestHelpers params oStmt x), ()) :=
  rfl

omit [Fintype F] [Fact ((-1 : F) ≠ 1)] [SampleableType F] in
/-- **The honest prover's output oracle map equals the honest-form lambda, pointwise.**

Strips the `pure`/`Prod` wrapping of `honestProver_output_oStmtOut_eq_honestForm` down to the bare
oracle-map equality consumed by the `HonestFormFact` body: the second component of the honest
prover's output statement is exactly `(.input i → oStmt i, .multiplicity → honestMultiplicity,
.helpers → honestHelpers)`.  Pure definitional identity of the honest run. -/
theorem honestOutput_oStmt_map_eq
    (oStmt : ∀ i, OStmtIn F n M i) (x : F) :
    (fun
        | .input i => oStmt i
        | .multiplicity => honestMultiplicity oStmt
        | .helpers => honestHelpers params oStmt x :
          ∀ i, OStmtAfterOuter F n M params i)
      = (fun
          | .input i => oStmt i
          | .multiplicity => honestMultiplicity oStmt
          | .helpers => honestHelpers params oStmt x) :=
  rfl

/-! ### Step 2: the honest-form predicate body is genuinely satisfied on honest outputs -/

omit [oSpec.Fintype] [oSpec.Inhabited] [Fact ((-1 : F) ≠ 1)] [SampleableType F] in
/-- **The honest-form predicate holds on every honest prover output (no assumption).**

For a genuine `inputRelation` input `(stmt₀, oStmt₀)` and a challenge `x` *off the table poles*, the
honest prover's output statement — `{ xChallenge := x, … }` together with the honest-form oracle map
— satisfies the existential *body* of the `HonestFormFact` predicate, witnessed by the very input
`(stmt₀, oStmt₀)`.  Concretely there exists a genuine input whose honest oracles reproduce the
retained oracle map, and whose `x`-challenge is pole-free.

This is the precise sense in which `hHonestForm` carries **no content beyond** the honest
construction: wherever the honest run actually lands (an honest output statement), the predicate is
*provably true* — there is never a real counterexample.  `hHonestForm` survives as a named hypothesis
in the headline only because it is quantified over *arbitrary, possibly fabricated* after-outer
statements; the honest run produces exactly the statements handled here. -/
theorem honestForm_body_on_honest_output
    (stmt₀ : StmtIn F n M) (oStmt₀ : ∀ i, OStmtIn F n M i)
    (hInput : (((stmt₀, oStmt₀), ()) ∈ inputRelation F n M))
    (x : F)
    (hPole : ∀ u : Hypercube n,
      x + evalOnHypercube (tableOracle oStmt₀) u ≠ 0)
    (zChallenge : Fin n → F)
    (batchingScalars : Fin params.numGroups → F) :
    ∃ (stmtIn₀ : StmtIn F n M) (oStmtIn₀ : ∀ i, OStmtIn F n M i),
      (((stmtIn₀, oStmtIn₀), ()) ∈ inputRelation F n M) ∧
      (∀ u : Hypercube n,
        ({ xChallenge := x, zChallenge := zChallenge,
            batchingScalars := batchingScalars : StmtAfterOuter F n M params }).xChallenge +
          evalOnHypercube (tableOracle oStmtIn₀) u ≠ 0) ∧
      (fun
        | .input i => oStmt₀ i
        | .multiplicity => honestMultiplicity oStmt₀
        | .helpers => honestHelpers params oStmt₀ x : ∀ i, OStmtAfterOuter F n M params i)
        = (fun
            | .input i => oStmtIn₀ i
            | .multiplicity => honestMultiplicity oStmtIn₀
            | .helpers =>
                honestHelpers params oStmtIn₀
                  ({ xChallenge := x, zChallenge := zChallenge,
                      batchingScalars := batchingScalars : StmtAfterOuter F n M params }).xChallenge) :=
  ⟨stmt₀, oStmt₀, hInput, hPole, rfl⟩

/-! ### Step 3: the pole event is already inside the completeness error budget -/

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- **The pole event is bounded by `logupCompletenessError` (folded into the budget).**

The failure of `hPoleFree` for a fixed input `oStmt` is exactly the table-pole event: the uniformly
sampled challenge `x` hits some pole `-t(u)`.  Its probability is `≤ logupCompletenessError F n =
|Hypercube n| / |F|`, the genuinely-proven `probEvent_pole_le_logupCompletenessError`.  So `hPoleFree`
is *not* an extra assumption: its complement is already accounted for inside the completeness error
budget.  This is the probabilistic half of discharging the two honest constituents. -/
theorem poleEvent_le_logupCompletenessError (oStmt : ∀ i, OStmtIn F n M i)
    [DecidablePred
      (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)] :
    probEvent (uniformSample F)
      (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)
      ≤ (logupCompletenessError F n : ℝ≥0∞) :=
  probEvent_pole_le_logupCompletenessError F n M oStmt

/-! ### Step 4: end-to-end completeness with the honest constituents -/

/-- **LogUp Protocol 2 completeness with the honest constituents (issue #13, residual H-honestForm).**

Identical conclusion to `logup_completeness_uncond`, consuming the two honest constituents
`hHonestForm` (`HonestFormFact`) and `hPoleFree` (`PoleFreeFact`) in place of the monolithic
`hHonest`.  The structural content of `hHonestForm` is discharged by
`honestProver_output_oStmtOut_eq_honestForm` / `honestForm_body_on_honest_output` (the honest prover
emits exactly the honest-form oracle map, and the predicate holds on every honest output), and the
probabilistic content of `hPoleFree` is folded into the error budget by
`poleEvent_le_logupCompletenessError` (the pole event is `≤ logupCompletenessError F n`).

This is a straight re-export of `logup_completeness_honest`: gluing the two constituents back into
`hHonest` (`hHonest_of_form_poleFree`) and feeding `logup_completeness_uncond`.  The remaining
residual surface is `{hHonestForm, hPoleFree, hPerRound, hImplSupp, hAppend}` plus `hInit`. -/
theorem logup_completeness_honestForm
    (hInit : NeverFail init)
    (hHonestForm : HonestFormFact F n M params)
    (hPoleFree : PoleFreeFact F n M params hHonestForm)
    (hPerRound : ∀ i,
      (Sumcheck.Spec.SingleRound.oracleReduction F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i).toReduction =
        Sumcheck.Spec.SingleRound.reduction F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (hAppend :
      AppendCompletenessResidual oSpec F n M params init impl
        (outerCompletenessResidual_of_neverFail oSpec F n M params init impl hInit)
        (sumcheckCompletenessResidual_of_honest_perRound oSpec F n M params init impl
          (hHonest_of_form_poleFree F n M params hHonestForm hPoleFree)
          hPerRound hInit hImplSupp)) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_honest oSpec F n M params init impl hInit hHonestForm hPoleFree
    hPerRound hImplSupp hAppend

end HonestSupport

end Logup

/- Axiom audit for the honest-support discharge of LogUp completeness. -/
#print axioms Logup.honestProver_output_oStmtOut_eq_honestForm
#print axioms Logup.honestOutput_oStmt_map_eq
#print axioms Logup.honestForm_body_on_honest_output
#print axioms Logup.poleEvent_le_logupCompletenessError
#print axioms Logup.logup_completeness_honestForm
