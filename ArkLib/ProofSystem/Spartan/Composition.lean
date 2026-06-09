/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SpartanBricks

/-!
# The composed Spartan PIOP oracle reduction (existence discharge of `composedPIOPResidual`)

`SpartanBricks.composedPIOPResidual` asserts the *existence* of a fully-composed Spartan oracle
reduction with input context the bare R1CS instance `(Statement, OracleStatement, Witness)` and
output context the terminal `(FinalStatement, FinalOracleStatement, Unit)`, over *some* combined
protocol spec. Its companion `composedPIOPResidual_of_reduction` records that this existence holds as
soon as *any* concrete `Rc` of that type is supplied — "the genuine open obligation is the
construction of `Rc`, with no remaining probabilistic or relational content."

This file discharges that construction by iterating `OracleReduction.append` over the seven Spartan
phases:

  firstMessage ▷ firstChallenge ▷ firstSumcheck ▷ sendEvalClaim ▷ linearCombination
              ▷ prependTarget ▷ secondSumcheck ▷ finalCheck

Two facts make the chain go through:

* **Witness threading** already lines up on the developed tree: `firstMessage` (a
  `SendSingleWitness` phase) outputs witness `Unit`, and every subsequent phase consumes/outputs
  `Unit`, so each `append` seam's witness types match definitionally.
* **`AppendCoherent` leaves.** `OracleReduction.append R₁ R₂` needs `AppendCoherent R₁.verifier`.
  With the chain **right-associated**, every left operand is a single phase (a *leaf*), so only the
  per-phase leaf instances are needed; those already exist for the six real phases
  (`instFirstMessageVerifierAppendCoherent`, …, `instSecondSumcheckVerifierAppendCoherent`). The
  composite `AppendCoherent` for any nested right operand is supplied automatically by
  `OracleVerifier.Append.AppendCoherent.oracleReductionAppend`.

The only new ingredient is **`prependTarget`**, a 0-round (`!p[]`) adapter bridging
`linearCombination`'s output statement `AfterLinearCombination` to `secondSumcheck`'s input statement
`R × AfterLinearCombination` (the leading `R` is the second sum-check's claimed target). It is a pure
statement map on an unchanged oracle-statement family, modeled on `CheckClaim.oracleReduction`; its
`AppendCoherent` instance is immediate (the embedding is `inl`, the oracle family is unchanged).

NB: `composedPIOPResidual` is purely a *typed-existence* statement. The honest second-sum-check
target value is threaded by the *completeness* layer (`composedCompletenessResidual`), where the
prover and verifier evaluate the bundled eval-claim oracle; here, `prependTarget` records the target
slot whose value the completeness layer pins.
-/

open OracleComp OracleInterface ProtocolSpec Function

namespace Spartan.Spec

noncomputable section

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] (pp : PublicParams)
variable {ι : Type} (oSpec : OracleSpec ι) [SampleableType R]

namespace Bricks

/-- The second-sum-check target slot prepended between `linearCombination` and `secondSumcheck`.
Its value is the claimed sum the second sum-check opens; it is pinned to the honest combination of
the bundled eval claims by the completeness layer. For the *existence* residual only the typed slot
matters, so it is recorded as a statement field carried by the adapter below. -/
@[reducible]
def secondSumcheckTargetSlot : Type := R

/-- **`prependTarget` prover.** Over the empty protocol `!p[]`, sends/receives nothing; it maps the
input context statement `AfterLinearCombination` to `R × AfterLinearCombination` by prepending the
target slot (here the default `0` slot — the honest value is pinned by the completeness layer), and
passes the oracle-statement family and `Unit` witness through unchanged. Modeled on
`CheckClaim.oracleProver`. -/
def prependTargetProver :
    OracleProver oSpec
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      (R × Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      !p[] where
  PrvState := fun _ => Statement.AfterLinearCombination R pp ×
    (∀ i, OracleStatement.AfterLinearCombination R pp i)
  input := Prod.fst
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun st => pure (((0, st.1), st.2), ())

/-- **`prependTarget` oracle verifier.** Maps the input statement to `R × AfterLinearCombination` by
prepending the target slot; the output oracle family is the input family unchanged (embedding `inl`).
Modeled on `CheckClaim.oracleVerifier`. -/
def prependTargetVerifier :
    OracleVerifier oSpec
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp)
      (R × Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp)
      !p[] where
  verify := fun stmt _ => pure (0, stmt)
  embed := Embedding.inl
  hEq := by intro i; simp

/-- **`prependTarget` oracle reduction** (the 0-round target-slot adapter). -/
def prependTarget :
    OracleReduction oSpec
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      (R × Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      !p[] where
  prover := prependTargetProver pp oSpec
  verifier := prependTargetVerifier pp oSpec

/-- The `prependTarget` verifier is append-coherent: its oracle-statement embedding is `inl` onto the
unchanged input family, so the coherence obligations reduce to `rfl`. -/
instance instPrependTargetVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (prependTargetVerifier pp oSpec) where
  hCohInl i k h := by
    dsimp [prependTargetVerifier] at h
    cases i <;> cases h <;> rfl
  hCohInr i k h := by
    dsimp [prependTargetVerifier] at h
    cases i <;> cases h <;> rfl

/-- **The fully-composed Spartan PIOP oracle reduction.** Right-associated iterated
`OracleReduction.append` over the seven phases (with the `prependTarget` target-slot adapter between
`linearCombination` and `secondSumcheck`). Every left operand is a leaf phase, so the required
`AppendCoherent` instances are exactly the per-phase leaves; the nested right composites get theirs
from `AppendCoherent.oracleReductionAppend`. -/
def composedPIOP_Rc :
    OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit
      _ :=
  (oracleReduction.firstMessage R pp oSpec).append <|
  (oracleReduction.firstChallenge R pp oSpec).append <|
  (firstSumcheckReduction pp oSpec).append <|
  (oracleReduction.sendEvalClaim R pp oSpec).append <|
  (oracleReduction.linearCombination R pp oSpec).append <|
  (prependTarget pp oSpec).append <|
  (secondSumcheckReduction pp oSpec).append <|
  (finalCheck R pp oSpec)

/-- **`composedPIOPResidual` discharged.** The composed reduction `composedPIOP_Rc` witnesses the
typed existence. -/
theorem composedPIOPResidual_holds_proof : composedPIOPResidual R pp oSpec :=
  composedPIOPResidual_of_reduction R pp oSpec (composedPIOP_Rc pp oSpec)

end Bricks

end

end Spartan.Spec
