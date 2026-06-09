/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.Basic
import ArkLib.ProofSystem.Spartan.FirstSumcheckReduction
import ArkLib.ProofSystem.Spartan.SecondSumcheckReduction
import ArkLib.ProofSystem.Component.CheckClaim
import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# Spartan PIOP — genuine 7-phase composition (issue #114)

This module assembles the full Spartan polynomial-IOP by iterated `OracleReduction.append` of the
seven phases

  `firstMessage ▷ firstChallenge ▷ firstSumcheck ▷ sendEvalClaim ▷ linearCombination`
  `  ▷ secondSumcheck ▷ finalCheck`

into a single concrete `OracleReduction` (over an explicit combined protocol spec), and discharges
the two existence residuals `composedPIOPResidual` / `composedPIOPWithClaimResidual` from
`ToMathlib/SpartanBricks.lean` as genuine constructed terms (no `sorry`, axiom-clean).

## What was needed to make the chain type-check and elaborate

Two concrete obstructions had to be resolved (they are recorded in the in-file comment of
`SpartanBricks.lean` ~1003):

1. **Target threading at the `linearCombination → secondSumcheck` seam.** `linearCombination`
   outputs the statement `Statement.AfterLinearCombination`, but `secondSumcheckReduction`'s input
   statement is `R × Statement.AfterLinearCombination` — it carries the (oracle-dependent) sum-check
   target out in front, exactly as the final `CheckClaim` carries `R × FinalStatement`. We bridge the
   seam with a zero-message **`prependTarget`** adapter that prepends a target field to the
   statement, leaving the oracle family unchanged. (The witness type is already `Unit` across every
   seam, so there is no witness-threading obstruction — the comment in `SpartanBricks.lean` about
   `firstChallenge` carrying `Witness R pp` is stale.)

2. **Instance synthesis through nested `++ₚ`.** `OracleReduction.append` re-synthesizes, for each
   left operand, both `∀ i, OracleInterface (pSpec.Message i)` and the
   `OracleVerifier.Append.AppendCoherent` side condition. For a deeply nested `++ₚ` these do *not*
   fire by bare `inferInstance` (the recursive `ProtocolSpec.instOracleInterfaceMessageAppend` /
   `AppendCoherent.append` instances are not found automatically). We therefore *name* each
   intermediate composite spec (`sp1 … sp5`, `spFinal`) and supply, at each step, the message
   `OracleInterface`, the challenge `SampleableType`, and the verifier `AppendCoherent` instance
   explicitly. This mirrors the single-append pattern used in `ProofSystem/Logup/Protocol.lean`,
   extended to the seven-phase chain. (`SampleableType (R1CS.MatrixIdx → R)` is supplied via
   `FinEnum R1CS.MatrixIdx`, which the linear-combination challenge needs.)

All `AppendCoherent` leaf instances already exist (`instFirstMessageVerifierAppendCoherent`,
`instFirstChallengeVerifierAppendCoherent`, `instFirstSumcheckVerifierAppendCoherent`,
`instSendEvalClaimVerifierAppendCoherent`, `instLinearCombinationVerifierAppendCoherent`,
`instSecondSumcheckVerifierAppendCoherent`); the only new leaf coherence is for `prependTarget`.
-/

open OracleComp OracleInterface ProtocolSpec Function

deriving instance Fintype for R1CS.MatrixIdx

namespace Spartan.Spec

namespace Composition

noncomputable section

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] (pp : PublicParams)
variable {ι : Type} (oSpec : OracleSpec ι) [SampleableType R]

/-- `FinEnum` for the three-element R1CS matrix index, used to make the linear-combination challenge
`R1CS.MatrixIdx → R` `SampleableType` (via `VCVio`'s `instSampleableTypeFunc`). -/
instance : FinEnum R1CS.MatrixIdx :=
  FinEnum.ofList [.A, .B, .C] (fun x => by cases x <;> simp)

/-! ## Terminal statement types

These mirror `SpartanBricks.FinalStatement` / `FinalOracleStatement` / `FinalClaimStatement` (each
reducible, so the two are defeq), kept here so this module does not depend on `SpartanBricks`. -/

/-- The terminal (non-oracle) statement after the second sum-check. -/
@[reducible] def FinalStatement : Type := Statement.AfterSecondSumcheck R pp

/-- The terminal oracle-statement family (unchanged from after the second sum-check). -/
@[reducible] def FinalOracleStatement : Fin 1 ⊕ (R1CS.MatrixIdx ⊕ Fin 1) → Type :=
  OracleStatement.AfterSecondSumcheck R pp

instance : ∀ i, OracleInterface (FinalOracleStatement R pp i) :=
  (inferInstance : ∀ i, OracleInterface (OracleStatement.AfterSecondSumcheck R pp i))

/-- The target-carrying terminal statement (target value in front of the Spartan context). -/
@[reducible] def FinalClaimStatement : Type := R × FinalStatement R pp

/-! ## `prependTarget` adapter

A zero-round oracle reduction `St ▷ R × St` that prepends a (constant) target field to the
statement, leaving the oracle family unchanged. Used (a) to bridge `linearCombination`'s output to
`secondSumcheckReduction`'s `R × _` input, and (b) to reach the target-carrying final check. For the
*existence* statement the prepended value is irrelevant; we use `0`. -/
def prependTargetVerifier (St : Type) {κ : Type} (OSt : κ → Type)
    [∀ i, OracleInterface (OSt i)] :
    OracleVerifier oSpec St OSt (R × St) OSt !p[] where
  verify := fun stmt _ => pure (0, stmt)
  embed := Embedding.inl
  hEq := fun _ => rfl

/-- The honest prover for `prependTarget`: forwards the statement & oracle family, prepending the
constant target `0`. -/
def prependTarget (St : Type) {κ : Type} (OSt : κ → Type)
    [∀ i, OracleInterface (OSt i)] :
    OracleReduction oSpec St OSt Unit (R × St) OSt Unit !p[] where
  prover := {
    PrvState := fun _ => St × (∀ i, OSt i)
    input := Prod.fst
    sendMessage := fun i => nomatch i
    receiveChallenge := fun i => nomatch i
    output := fun ⟨stmt, oStmt⟩ => pure (((0, stmt), oStmt), ())
  }
  verifier := prependTargetVerifier R oSpec St OSt

instance instPrependTargetCoh (St : Type) {κ : Type} (OSt : κ → Type)
    [∀ i, OracleInterface (OSt i)] :
    OracleVerifier.Append.AppendCoherent (prependTargetVerifier R oSpec St OSt) where
  hCohInl i k h := by
    simp only [prependTargetVerifier, Function.Embedding.inl_apply] at h
    obtain rfl := Sum.inl.inj h
    rfl
  hCohInr i k h := by
    simp only [prependTargetVerifier, Function.Embedding.inl_apply] at h
    cases h

instance instPrependTargetRedCoh (St : Type) {κ : Type} (OSt : κ → Type)
    [∀ i, OracleInterface (OSt i)] :
    OracleVerifier.Append.AppendCoherent (prependTarget R oSpec St OSt).verifier :=
  instPrependTargetCoh R oSpec St OSt

/-! ## Bridge `AppendCoherent` instances

`sendEvalClaim` / `linearCombination` carry their `AppendCoherent` instance on the *verifier* def
rather than on `(oracleReduction.…).verifier`; bridge them (the two are defeq). -/

instance instSendEvalClaimRedCoh :
    OracleVerifier.Append.AppendCoherent (oracleReduction.sendEvalClaim R pp oSpec).verifier :=
  instSendEvalClaimVerifierAppendCoherent R pp oSpec

instance instLinearCombinationRedCoh :
    OracleVerifier.Append.AppendCoherent (oracleReduction.linearCombination R pp oSpec).verifier :=
  instLinearCombinationVerifierAppendCoherent R pp oSpec

/-! ## Explicit composite protocol specs -/

@[reducible] def sp1 : ProtocolSpec (1 + 1) :=
  (⟨!v[Direction.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1) ++ₚ
  (⟨!v[Direction.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1)
@[reducible] def sp2 := sp1 R pp ++ₚ Sumcheck.Spec.pSpec R 3 pp.ℓ_m
@[reducible] def sp3 := sp2 R pp ++ₚ (⟨!v[Direction.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1)
@[reducible] def sp4 := sp3 R pp ++ₚ (⟨!v[Direction.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1)
@[reducible] def sp4b := sp4 R pp ++ₚ (!p[] : ProtocolSpec 0)
@[reducible] def sp5 := sp4b R pp ++ₚ Sumcheck.Spec.pSpec R 2 pp.ℓ_n
@[reducible] def spFinal := sp5 R pp ++ₚ (!p[] : ProtocolSpec 0)
@[reducible] def spFinalClaim := spFinal R pp ++ₚ (!p[] : ProtocolSpec 0)

instance : ∀ i, OracleInterface ((sp1 R pp).Message i) := ProtocolSpec.instOracleInterfaceMessageAppend
instance : ∀ i, SampleableType ((sp1 R pp).Challenge i) := ProtocolSpec.instSampleableTypeChallengeAppend
instance : ∀ i, OracleInterface ((sp2 R pp).Message i) := ProtocolSpec.instOracleInterfaceMessageAppend
instance : ∀ i, SampleableType ((sp2 R pp).Challenge i) := ProtocolSpec.instSampleableTypeChallengeAppend
instance : ∀ i, OracleInterface ((sp3 R pp).Message i) := ProtocolSpec.instOracleInterfaceMessageAppend
instance : ∀ i, SampleableType ((sp3 R pp).Challenge i) := ProtocolSpec.instSampleableTypeChallengeAppend
instance : ∀ i, OracleInterface ((sp4 R pp).Message i) := ProtocolSpec.instOracleInterfaceMessageAppend
instance : ∀ i, SampleableType ((sp4 R pp).Challenge i) := ProtocolSpec.instSampleableTypeChallengeAppend
instance : ∀ i, OracleInterface ((sp4b R pp).Message i) := ProtocolSpec.instOracleInterfaceMessageAppend
instance : ∀ i, SampleableType ((sp4b R pp).Challenge i) := ProtocolSpec.instSampleableTypeChallengeAppend
instance : ∀ i, OracleInterface ((sp5 R pp).Message i) := ProtocolSpec.instOracleInterfaceMessageAppend
instance : ∀ i, SampleableType ((sp5 R pp).Challenge i) := ProtocolSpec.instSampleableTypeChallengeAppend
instance : ∀ i, OracleInterface ((spFinal R pp).Message i) := ProtocolSpec.instOracleInterfaceMessageAppend
instance : ∀ i, SampleableType ((spFinal R pp).Challenge i) := ProtocolSpec.instSampleableTypeChallengeAppend
instance : ∀ i, OracleInterface ((spFinalClaim R pp).Message i) := ProtocolSpec.instOracleInterfaceMessageAppend
instance : ∀ i, SampleableType ((spFinalClaim R pp).Challenge i) := ProtocolSpec.instSampleableTypeChallengeAppend

/-! ## The composed reduction, phase by phase -/

/-- `firstMessage ▷ firstChallenge`. -/
def step1 : OracleReduction oSpec (Statement R pp) (OracleStatement R pp) (Witness R pp)
    (Statement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstChallenge R pp) Unit (sp1 R pp) :=
  (oracleReduction.firstMessage R pp oSpec).append (oracleReduction.firstChallenge R pp oSpec)
instance instStep1Coh : OracleVerifier.Append.AppendCoherent (step1 R pp oSpec).verifier :=
  OracleVerifier.Append.AppendCoherent.append _ _

/-- `step1 ▷ firstSumcheck`. -/
def step2 : OracleReduction oSpec (Statement R pp) (OracleStatement R pp) (Witness R pp)
    (Statement.AfterFirstSumcheck R pp) (OracleStatement.AfterFirstSumcheck R pp) Unit (sp2 R pp) :=
  (step1 R pp oSpec).append (firstSumcheckReduction pp oSpec)
instance instStep2Coh : OracleVerifier.Append.AppendCoherent (step2 R pp oSpec).verifier :=
  OracleVerifier.Append.AppendCoherent.append _ _

/-- `step2 ▷ sendEvalClaim`. -/
def step3 : OracleReduction oSpec (Statement R pp) (OracleStatement R pp) (Witness R pp)
    (Statement.AfterSendEvalClaim R pp) (OracleStatement.AfterSendEvalClaim R pp) Unit (sp3 R pp) :=
  (step2 R pp oSpec).append (oracleReduction.sendEvalClaim R pp oSpec)
instance instStep3Coh : OracleVerifier.Append.AppendCoherent (step3 R pp oSpec).verifier :=
  OracleVerifier.Append.AppendCoherent.append _ _

/-- `step3 ▷ linearCombination`. -/
def step4 : OracleReduction oSpec (Statement R pp) (OracleStatement R pp) (Witness R pp)
    (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit (sp4 R pp) :=
  (step3 R pp oSpec).append (oracleReduction.linearCombination R pp oSpec)
instance instStep4Coh : OracleVerifier.Append.AppendCoherent (step4 R pp oSpec).verifier :=
  OracleVerifier.Append.AppendCoherent.append _ _

/-- `step4 ▷ prependTarget` — bridge to the `R × _` input of the second sum-check. -/
def step4b : OracleReduction oSpec (Statement R pp) (OracleStatement R pp) (Witness R pp)
    (R × Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit (sp4b R pp) :=
  (step4 R pp oSpec).append
    (prependTarget R oSpec (Statement.AfterLinearCombination R pp)
      (OracleStatement.AfterLinearCombination R pp))
instance instStep4bCoh : OracleVerifier.Append.AppendCoherent (step4b R pp oSpec).verifier :=
  OracleVerifier.Append.AppendCoherent.append _ _

/-- `step4b ▷ secondSumcheck`. -/
def step5 : OracleReduction oSpec (Statement R pp) (OracleStatement R pp) (Witness R pp)
    (Statement.AfterSecondSumcheck R pp) (OracleStatement.AfterSecondSumcheck R pp) Unit (sp5 R pp) :=
  (step4b R pp oSpec).append (secondSumcheckReduction (R := R) pp oSpec)
instance instStep5Coh : OracleVerifier.Append.AppendCoherent (step5 R pp oSpec).verifier :=
  OracleVerifier.Append.AppendCoherent.append _ _

/-- The final `CheckClaim` phase over the terminal statement. For the existence statement the
predicate is irrelevant, so we use the trivially-true one. -/
def finalPhase :
    OracleReduction oSpec (FinalStatement R pp) (FinalOracleStatement R pp) Unit
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit !p[] :=
  CheckClaim.oracleReduction oSpec (FinalStatement R pp) (FinalOracleStatement R pp)
    (fun _ => pure True)

/-- **The fully composed Spartan PIOP oracle reduction.** Input context is the bare R1CS instance
`(Statement, OracleStatement, Witness)`; output context is the terminal Spartan statement after the
final check, with output witness `Unit`. Obtained by iterated `OracleReduction.append` of the seven
phases (plus the `prependTarget` seam adapter). -/
def composedPIOP :
    OracleReduction oSpec (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit (spFinal R pp) :=
  (step5 R pp oSpec).append (finalPhase R pp oSpec)

/-- `step5 ▷ prependTarget` — bridge to the target-carrying final check. -/
def step5b :
    OracleReduction oSpec (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (R × FinalStatement R pp) (FinalOracleStatement R pp) Unit (spFinal R pp) :=
  (step5 R pp oSpec).append
    (prependTarget R oSpec (FinalStatement R pp) (FinalOracleStatement R pp))
instance instStep5bCoh : OracleVerifier.Append.AppendCoherent (step5b R pp oSpec).verifier :=
  OracleVerifier.Append.AppendCoherent.append _ _

/-- The target-carrying final `CheckClaim` phase. -/
def finalPhaseClaim :
    OracleReduction oSpec (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit !p[] :=
  CheckClaim.oracleReduction oSpec (FinalClaimStatement R pp) (FinalOracleStatement R pp)
    (fun _ => pure True)

/-- **The fully composed Spartan PIOP oracle reduction, target-carrying endpoint.** Same as
`composedPIOP` but ending at the real target-carrying `CheckClaim` (`FinalClaimStatement`). -/
def composedPIOPWithClaim :
    OracleReduction oSpec (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit (spFinalClaim R pp) :=
  (step5b R pp oSpec).append (finalPhaseClaim R pp oSpec)

/-! ## Existence theorems (the two residuals, as genuine constructed terms) -/

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- **Existence of the composed Spartan PIOP.** Discharges `composedPIOPResidual`. -/
theorem composedPIOP_nonempty :
    ∃ (N : ℕ) (pSpecC : ProtocolSpec N) (_ : ∀ i, OracleInterface.{0, 0} (pSpecC.Message i))
      (_ : ∀ i, SampleableType (pSpecC.Challenge i)),
      Nonempty (OracleReduction oSpec
        (Statement R pp) (OracleStatement R pp) (Witness R pp)
        (Statement.AfterSecondSumcheck R pp) (OracleStatement.AfterSecondSumcheck R pp) Unit pSpecC) :=
  ⟨_, spFinal R pp, inferInstance, inferInstance, ⟨composedPIOP R pp oSpec⟩⟩

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- **Existence of the target-carrying composed Spartan PIOP.** Discharges
`composedPIOPWithClaimResidual`. -/
theorem composedPIOPWithClaim_nonempty :
    ∃ (N : ℕ) (pSpecC : ProtocolSpec N) (_ : ∀ i, OracleInterface.{0, 0} (pSpecC.Message i))
      (_ : ∀ i, SampleableType (pSpecC.Challenge i)),
      Nonempty (OracleReduction oSpec
        (Statement R pp) (OracleStatement R pp) (Witness R pp)
        (R × Statement.AfterSecondSumcheck R pp) (OracleStatement.AfterSecondSumcheck R pp) Unit pSpecC) :=
  ⟨_, spFinalClaim R pp, inferInstance, inferInstance, ⟨composedPIOPWithClaim R pp oSpec⟩⟩

end

end Composition

end Spartan.Spec
