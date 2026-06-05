import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.ProofSystem.Logup.Protocol

/-!
# LogUp Completeness

Main completeness statement for Protocol 2 of `paper.txt`.

## Proof architecture and the upstream `sorryAx` wall

`logupOracleReduction` is *definitionally* the sequential composition
`outerOracleReduction.append sumcheckOracleReduction` (see `logupOracleReduction_eq_append`).
Completeness therefore follows from `OracleReduction.append_completeness`, supplying:

* outer-phase completeness with error `logupCompletenessError F n` (the pole-rejection error,
  whose mathematical content is the genuinely-proven `card_poleSet_le` / `probEvent_pole_le`
  below: a uniformly sampled `x : F` hits a table pole `-t(u)` with probability at most
  `|Hypercube n| / |F|`), and
* embedded-sumcheck completeness with error `0` (the honest sumcheck run is deterministic and
  correct).

Both sub-facts, and the composition lemma `OracleReduction.append_completeness` itself, are blocked
by `sorryAx` introduced *outside* `ArkLib/ProofSystem/Logup/**`, which this development is not
permitted to modify:

* `OracleVerifier.Append.emitOStmt₂Query`
  (`ArkLib/OracleReduction/Composition/Sequential/Append.lean:277`) is a `sorry` — the
  "instance-coherence gap (#433)" for routing the first verifier's output-oracle queries. Because
  `logupVerifier = OracleVerifier.append outerVerifier sumcheckVerifier` and the generic sumcheck
  verifier `Sumcheck.Spec.oracleVerifier` is itself `OracleVerifier.seqCompose` (built recursively
  from `OracleVerifier.append`), `logupOracleReduction` *itself* depends on `sorryAx`. Any theorem
  whose statement mentions `logupOracleReduction` consequently reports `sorryAx`, independent of how
  it is proved.
* `Reduction.append_completeness`
  (`ArkLib/OracleReduction/Composition/Sequential/Append.lean:1097`) is a `sorry`; the oracle-level
  `OracleReduction.append_completeness` reduces to it.
* `Sumcheck.Spec.oracleVerifier` / `Sumcheck.Spec.oracleReduction` carry `sorryAx` via the same
  `OracleVerifier.append` route, so embedded-sumcheck completeness is not yet provable in-tree.

Consequently `logup_completeness` is closed via the genuine composition skeleton, with a single
residual `sorry` (`subPhaseCompleteness`) standing for the two upstream-blocked sub-completeness
facts. The pole-probability lemmas it relies on are fully proven (no `sorryAx`).
-/

open scoped NNReal ENNReal

open OracleComp

-- Elaborating the sub-phase completeness statement over the embedded sumcheck `pSpec` is heavy;
-- give the elaborator extra budget.
set_option maxHeartbeats 800000

namespace Logup

section PoleBound

variable (F : Type) [Field F] [Fintype F] [DecidableEq F]
variable (n M : ℕ)

set_option linter.unusedDecidableInType false in
/-- The number of "bad" verifier challenges `x` — those hitting a table pole `-t(u)` on some
hypercube row `u` — is at most `|Hypercube n|` (at most one pole per row).

This is the combinatorial heart of the LogUp completeness error: the honest prover/verifier run is
deterministic and correct *except* when the sampled `x` is one of these poles, and there are at most
`|Hypercube n|` of them. Fully proven (no `sorryAx`). -/
theorem card_poleSet_le (oStmt : ∀ i, OStmtIn F n M i)
    [DecidablePred
      (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)] :
    (Finset.univ.filter
        (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)).card
      ≤ Fintype.card (Hypercube n) := by
  classical
  -- Every bad `x` equals `-t(u)` for some `u`, so the bad set embeds into the image of
  -- `u ↦ -t(u)`, which has at most `|Hypercube n|` elements.
  have hsub : (Finset.univ.filter
      (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)) ⊆
      Finset.univ.image (fun u : Hypercube n => - evalOnHypercube (tableOracle oStmt) u) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨u, hu⟩ := hx
    refine Finset.mem_image.mpr ⟨u, Finset.mem_univ _, ?_⟩
    linear_combination -hu
  calc (Finset.univ.filter
        (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)).card
      ≤ (Finset.univ.image
          (fun u : Hypercube n => - evalOnHypercube (tableOracle oStmt) u)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Hypercube n)).card := Finset.card_image_le
    _ = Fintype.card (Hypercube n) := by rw [Finset.card_univ]

set_option linter.unusedDecidableInType false in
/-- The probability that a uniformly sampled challenge `x : F` is a table pole is at most
`|Hypercube n| / |F|` — exactly the LogUp completeness error.

Fully proven (no `sorryAx`); this is the probabilistic statement of `card_poleSet_le`. -/
theorem probEvent_pole_le [SampleableType F] (oStmt : ∀ i, OStmtIn F n M i)
    [DecidablePred
      (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)] :
    probEvent (uniformSample F)
      (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)
      ≤ (Fintype.card (Hypercube n) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  rw [probEvent_uniformSample]
  exact ENNReal.div_le_div_right (by exact_mod_cast card_poleSet_le F n M oStmt) _

end PoleBound

section Completeness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances. -/
local instance : Inhabited F := ⟨0⟩

/-- Completeness error forced by the current rejection-based model of the `x` challenge.

Protocol 2 samples `x` from the complement of the table poles. The current verifier samples from
all of `F` and rejects poles, so the intended completeness statement carries this explicit bad-`x`
probability. Once the challenge sampler is modeled as the complement distribution, this should
collapse to perfect completeness.

The numerator `|Hypercube n|` is exactly the pole count bounded by `card_poleSet_le`.
-/
noncomputable def logupCompletenessError (F : Type) [Fintype F] (n : ℕ) : ℝ≥0 :=
  (Fintype.card (Hypercube n) : ℝ≥0) / (Fintype.card F)

/-- The trivial intermediate relation threaded between the outer LogUp phase and the embedded
sumcheck (the outer phase carries no witness obligation into the sumcheck). -/
def midRelation : Set ((StmtAfterOuter F n M params ×
    (∀ i, OStmtAfterOuter F n M params i)) × Unit) := Set.univ

/-- The full LogUp oracle reduction is, definitionally, the sequential composition of the outer
phase and the embedded sumcheck phase. This is the structural fact driving the completeness proof
via `OracleReduction.append_completeness`. -/
theorem logupOracleReduction_eq_append :
    logupOracleReduction oSpec F n M params =
      OracleReduction.append (outerOracleReduction oSpec F n M params)
        (sumcheckOracleReduction oSpec F n M params) := rfl

/-- The two sub-phase completeness obligations of the LogUp composition.

* The outer phase (`outerOracleReduction`) is complete with error `logupCompletenessError F n`: its
  honest run is deterministic and correct except when the sampled `x` is one of the at most
  `|Hypercube n|` table poles (see `probEvent_pole_le`); the verifier's pole-rejection `guard` then
  fails.
* The embedded sumcheck (`sumcheckOracleReduction`) is complete with error `0`.

WALL (upstream `sorryAx`, outside `ArkLib/ProofSystem/Logup/**`, not modifiable here):

* Outer completeness requires unfolding `Reduction.run (outerOracleReduction …)`. The prover and
  verifier of the outer phase are themselves `sorryAx`-free, and the failure event is exactly the
  pole event bounded by `probEvent_pole_le`. This direction is in principle closable in-tree but is
  not finished here.
* Sumcheck completeness is blocked: `sumcheckOracleReduction` is a `liftContext` of
  `Sumcheck.Spec.oracleReduction`, whose verifier `Sumcheck.Spec.oracleVerifier` is built from
  `OracleVerifier.seqCompose`/`OracleVerifier.append` and depends on the `sorry` at
  `ArkLib/OracleReduction/Composition/Sequential/Append.lean:277`
  (`OracleVerifier.Append.emitOStmt₂Query`). No `Sumcheck.Spec` completeness theorem exists in-tree.

Hence this single residual `sorry`. -/
theorem subPhaseCompleteness :
    (outerOracleReduction oSpec F n M params).completeness init impl
        (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n) ∧
      (sumcheckOracleReduction oSpec F n M params).completeness init impl
        (midRelation F n M params) outputRelation 0 := by
  sorry

/-- Main ArkLib completeness theorem for LogUp Protocol 2.

Reduced to `subPhaseCompleteness` through the genuine sequential-composition completeness lemma
`OracleReduction.append_completeness` (itself upstream-blocked by `sorryAx`; see the module
docstring). The completeness error `logupCompletenessError F n = |Hypercube n| / |F|` is the sum
`logupCompletenessError F n + 0` of the outer pole-rejection error and the (perfect) sumcheck
error. -/
theorem logup_completeness :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) := by
  obtain ⟨hOuter, hSum⟩ := subPhaseCompleteness oSpec F n M params init impl
  -- `logupOracleReduction` is definitionally `append outerOracleReduction sumcheckOracleReduction`
  -- (`logupOracleReduction_eq_append`), so the composed completeness fact unifies with the goal up
  -- to `logupCompletenessError F n + 0 = logupCompletenessError F n`. We assemble the composed fact
  -- and close by `simpa`, avoiding a `rw` that would force `whnf` of the full reduction.
  have h := OracleReduction.append_completeness.{0, 0, 0, 0}
    (rel₂ := midRelation F n M params)
    (outerOracleReduction oSpec F n M params)
    (sumcheckOracleReduction oSpec F n M params)
    hOuter hSum
  simpa only [add_zero] using h

end Completeness

end Logup
