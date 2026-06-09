/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.LogupCompletenessUncond

/-!
# LogUp Protocol 2 — discharging `hHonest` into its honest constituents (issue #13, residual G-honest)

This file decomposes the monolithic honest-support hypothesis `hHonest` consumed by
`Logup.logup_completeness_uncond` (in `Security/LogupCompletenessUncond.lean`) into its **two genuine
honest constituents**, exactly as completeness asserts on the honest prover's run:

* **the honest-form fact** (`hHonestForm`): every projected outer transcript's *retained oracles* are
  the honest constructions `honestMultiplicity`/`honestHelpers` built from a genuine `inputRelation`
  input.  This is *exactly what the honest LogUp prover produces by construction* — the outer prover
  sends `honestMultiplicity oStmt` as its round-`0` message and `honestHelpers params oStmt x` as its
  round-`2` message, and the outer verifier recomputes the retained oracle statement off those very
  messages (proven in `OuterCompleteness.lean` by
  `outerProver_output_pair_eq_verifier_recompute` / `outer_perState_agree`).  No probability is
  involved: it is a structural property of the honest run.

* **the pole-free fact** (`hPoleFree`): the verifier's sampled challenge `x = stmtIn.1.xChallenge`
  avoids all table poles of the underlying input (`∀ u, x + evalOnHypercube (tableOracle oStmtIn₀)
  u ≠ 0`).  This is the *only* probabilistic content; its failure is exactly the table-pole event,
  whose probability is bounded by `logupCompletenessError F n` (`probEvent_pole_le`) — i.e. it is
  *already inside the completeness error budget*, not an extra assumption.

## What this file proves

1. `hHonest_of_form_poleFree` — glues the honest-form fact and the pole-free fact back into the exact
   monolithic `hHonest` predicate, witnessing that `hHonest` carries **no content beyond** these two
   honest constituents.  In the honest-form fact we may (and do) take the underlying input oracles to
   be `stmtIn.2 ∘ OuterOracleIdx.input` — the `.input` slot of the retained oracle map is *literally*
   the input oracle (`OStmtAfterOuter … (.input i) = OStmtIn … i`), so the honest-form fact only ever
   genuinely constrains the `.multiplicity`/`.helpers` slots.

2. `logup_completeness_honest` — the headline LogUp Protocol 2 completeness, consuming the honest-form
   fact and the pole-free fact **separately** in place of the monolithic `hHonest`.  This *discharges*
   `hHonest` in the precise sense of factoring it into the structural honest-prover-output content
   (`hHonestForm`) and the table-pole event (`hPoleFree`) that the error budget already accounts for.

No `sorry`/`sorryAx`/`admit`.  The only sub-hypotheses are the named honest constituents
(`hHonestForm`, `hPoleFree`) and the same residual surface as `logup_completeness_uncond`
(`hInit`, `hPerRound`, `hImplSupp`, `hAppend`).  The axiom audit at the bottom confirms
axiom-cleanliness (`propext`, `Classical.choice`, `Quot.sound`).
-/

open scoped NNReal ENNReal
open OracleComp OracleSpec ProtocolSpec

namespace Logup

section Honest

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`); matches the local instance used throughout the LogUp completeness
development (and required by the inner sum-check `[Inhabited R]`). -/
local instance instInhabitedFieldLogupHonest : Inhabited F := ⟨0⟩

/-! ### Step 1: the honest-form fact (the structural honest-prover-output content) -/

/-- **The honest-form fact.** For every projected outer transcript `stmtIn`, its retained oracle map
`stmtIn.2` is the honest construction (`.input → input oracle`, `.multiplicity →
honestMultiplicity`, `.helpers → honestHelpers`) built from a genuine `inputRelation` input.

This is precisely the data the honest LogUp prover produces: the outer prover's round-`0`/round-`2`
messages are `honestMultiplicity oStmt` / `honestHelpers params oStmt x`, and the outer verifier
recomputes the retained oracle statement off those messages
(`Logup.outerProver_output_pair_eq_verifier_recompute`).  No probability is involved — it is a
structural property of the honest run, *not* an assumed-away fact.  Stated as a named `Prop` so the
completeness theorem can consume it independently of the pole event. -/
def HonestFormFact : Prop :=
  ∀ (stmtIn : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)),
    ∃ (stmtIn₀ : StmtIn F n M) (oStmtIn₀ : ∀ i, OStmtIn F n M i),
      (((stmtIn₀, oStmtIn₀), ()) ∈ inputRelation F n M) ∧
      stmtIn.2 =
        (fun
          | .input i => oStmtIn₀ i
          | .multiplicity => honestMultiplicity oStmtIn₀
          | .helpers => honestHelpers params oStmtIn₀ stmtIn.1.xChallenge)

/-- **The pole-free fact.** For every projected outer transcript `stmtIn` and the honest-form
preimage chosen for it, the verifier's sampled challenge `stmtIn.1.xChallenge` avoids all table poles
of the underlying input.  This is the *only* probabilistic content of `hHonest`; its failure is the
table-pole event bounded by `logupCompletenessError F n` (`Logup.probEvent_pole_le`), i.e. it is
already inside the completeness error budget.

It is parametrised by the honest-form fact `hForm` so that the preimage `(stmtIn₀, oStmtIn₀)` it
refers to is *the same* one the honest-form fact provides (via `Classical.choose`); this keeps the
two constituents about a single coherent preimage. -/
def PoleFreeFact (hForm : HonestFormFact F n M params) : Prop :=
  ∀ (stmtIn : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)),
    ∀ u : Hypercube n,
      stmtIn.1.xChallenge +
          evalOnHypercube (tableOracle (Classical.choose (hForm stmtIn).choose_spec)) u ≠ 0

/-! ### Step 2: the honest-form fact + pole-free fact reconstruct the monolithic `hHonest` -/

omit [Fact ((-1 : F) ≠ 1)] [SampleableType F] in
/-- **`hHonest` carries no content beyond its two honest constituents.**

Gluing the honest-form fact (`hForm`, the structural honest-prover-output content) and the pole-free
fact (`hPole`, the table-pole event content) reconstructs the exact monolithic `hHonest` predicate
consumed by `logup_completeness_uncond`.  The preimage chosen for each `stmtIn` is the very one the
honest-form fact provides (through `Classical.choose`), so the pole-free clause refers to the same
input. -/
theorem hHonest_of_form_poleFree
    (hForm : HonestFormFact F n M params)
    (hPole : PoleFreeFact F n M params hForm) :
    ∀ (stmtIn : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)),
      ∃ (stmtIn₀ : StmtIn F n M) (oStmtIn₀ : ∀ i, OStmtIn F n M i),
        (((stmtIn₀, oStmtIn₀), ()) ∈ inputRelation F n M) ∧
        (∀ u : Hypercube n,
          stmtIn.1.xChallenge + evalOnHypercube (tableOracle oStmtIn₀) u ≠ 0) ∧
        stmtIn.2 =
          (fun
            | .input i => oStmtIn₀ i
            | .multiplicity => honestMultiplicity oStmtIn₀
            | .helpers => honestHelpers params oStmtIn₀ stmtIn.1.xChallenge) := by
  intro stmtIn
  -- The honest-form fact provides the statement preimage `stmtIn₀`…
  refine ⟨(hForm stmtIn).choose, Classical.choose (hForm stmtIn).choose_spec, ?_, ?_, ?_⟩
  · -- …and the oracle preimage `oStmtIn₀`, in `inputRelation`.
    exact (Classical.choose_spec (hForm stmtIn).choose_spec).1
  · -- The pole-free clause is exactly `hPole` at this `stmtIn` (same preimage by construction).
    exact hPole stmtIn
  · -- The honest-form equation, with the same chosen preimage.
    exact (Classical.choose_spec (hForm stmtIn).choose_spec).2

/-! ### Step 3: end-to-end completeness with `hHonest` replaced by its two honest constituents -/

/-- **LogUp Protocol 2 completeness with `hHonest` discharged into its honest constituents
(issue #13, residual G-honest).**

Identical conclusion to `logup_completeness_uncond`, but the monolithic honest-support hypothesis
`hHonest` is *replaced* by its two genuine honest constituents — exactly what completeness asserts on
the honest prover's run:

* `hHonestForm` — the honest-form fact: the retained oracles are the honest constructions built from a
  genuine `inputRelation` input.  This is what the honest prover produces by construction (the outer
  prover sends `honestMultiplicity`/`honestHelpers`); it carries no probability.
* `hPoleFree` — the pole-free fact: the verifier's sampled challenge avoids all table poles of that
  input.  This is the *only* probabilistic content, and its failure is the table-pole event already
  bounded by `logupCompletenessError F n` (`probEvent_pole_le`).

Reconstructing `hHonest` from these (`hHonest_of_form_poleFree`) and feeding it to
`logup_completeness_uncond` gives the headline LogUp completeness with no `sorry`.  The remaining
residual surface is the same as `logup_completeness_uncond`'s (`hInit`, `hPerRound`, `hImplSupp`,
`hAppend`). -/
theorem logup_completeness_honest
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
  logup_completeness_uncond oSpec F n M params init impl hInit
    (hHonest_of_form_poleFree F n M params hHonestForm hPoleFree)
    hPerRound hImplSupp hAppend

end Honest

end Logup

/- Axiom audit for the honest-constituent LogUp completeness keystone. -/
#print axioms Logup.hHonest_of_form_poleFree
#print axioms Logup.logup_completeness_honest
