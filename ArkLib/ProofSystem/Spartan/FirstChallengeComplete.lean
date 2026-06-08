/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.ZeroCheckComplete
import ArkLib.OracleReduction.LiftContext.Lens

/-!
# First-challenge lens completeness (issue #114)

The Spartan first sum-check lifts the generic `RandomQuery` oracle reduction onto the virtual
zero-check polynomial `𝒢` via `firstChallengeContextLens`. Transferring `RandomQuery`'s perfect
completeness through that `liftContext` requires the value-level completeness side condition
`OracleContext.Lens.IsComplete`: an honest (R1CS-satisfying) outer instance must project to a valid
`RandomQuery` inner instance, and the inner output relation must lift back to a valid outer output
relation.

`firstChallenge_isComplete` discharges that obligation against the natural R1CS relations:
* `fcRelIn` — the outer input relation is the R1CS relation `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`
  (the witness component is unused, since `𝕫` reads the committed witness oracle `oStmt (.inr 0)`);
* `fcRelOut` — the outer output relation after the challenge is the *same* R1CS instance (the
  matrices/public-input/witness oracle are carried through unchanged; the sampled challenge `τ` is
  recorded but does not affect satisfiability).

`proj_complete` is exactly the zero-check completeness `zeroCheckVirtualPolynomial_eq_zero_of_satisfied`
(R1CS satisfied ⟹ `𝒢 = 0` ⟹ the two `RandomQuery` virtual oracles `(𝒢, 0)` are equal), and
`lift_complete` is the R1CS-preservation through the lift (independent of the coherence/compat data).
Together with the first-challenge coherence instance, this is the value-level half of the first
sum-check's completeness transfer.
-/

open MvPolynomial Matrix OracleSpec OracleComp

namespace Spartan.Spec

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R]
    (pp : Spartan.PublicParams) [SampleableType R]

/-- Outer (R1CS) input relation for the first-challenge phase. The `Witness` component is unused:
`𝕫 = 𝕩 ‖ (oStmt (.inr 0))` reads the *committed witness oracle*. -/
def fcRelIn :
    Set ((Statement.AfterFirstMessage R pp × ∀ i, OracleStatement.AfterFirstMessage R pp i)
      × Witness R pp) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1 (fun i => x.1.2 (.inl i)) (x.1.2 (.inr 0)) }

/-- Outer output relation after the first challenge: the same R1CS instance still holds. -/
def fcRelOut :
    Set ((Statement.AfterFirstChallenge R pp × ∀ i, OracleStatement.AfterFirstChallenge R pp i)
      × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2 (fun i => x.1.2 (.inl i)) (x.1.2 (.inr 0)) }

/-- **First-challenge lens completeness.** The first-challenge context lens carries R1CS-satisfying
instances to the `RandomQuery` input relation (`𝒢 = 0`) and lifts the inner output relation back to
the preserved R1CS output relation. `lift_complete` does not use the coherence/compat hypothesis, so
the statement holds for any `compat`. -/
@[reducible] def firstChallenge_isComplete
    (compat : (Statement.AfterFirstMessage R pp ×
          ∀ i, OracleStatement.AfterFirstMessage R pp i) × Witness R pp →
        (RandomQuery.StmtOut (MvPolynomial (Fin pp.ℓ_m) R) ×
          ∀ i, RandomQuery.OStmtOut (MvPolynomial (Fin pp.ℓ_m) R) i) × RandomQuery.WitOut → Prop) :
    Context.Lens.IsComplete (fcRelIn R pp)
      (RandomQuery.relIn (MvPolynomial (Fin pp.ℓ_m) R))
      (fcRelOut R pp)
      (RandomQuery.relOut (MvPolynomial (Fin pp.ℓ_m) R))
      compat
      (firstChallengeContextLens R pp).toContext where
  proj_complete := by
    rintro ⟨𝕩, oStmt⟩ wit hRelIn
    simp only [fcRelIn, Set.mem_setOf_eq] at hRelIn
    simp only [firstChallengeContextLens, OracleContext.Lens.toContext, Context.Lens.proj,
      firstChallengeStmtLens, OracleStatement.Lens.proj, RandomQuery.relIn, Set.mem_setOf_eq]
    exact zeroCheckVirtualPolynomial_eq_zero_of_satisfied pp 𝕩 oStmt hRelIn
  lift_complete := by
    rintro ⟨𝕩, oStmt⟩ wit ⟨q, oStmtOut⟩ _ _ hRelIn _
    simp only [fcRelIn, Set.mem_setOf_eq] at hRelIn
    simp only [firstChallengeContextLens, OracleContext.Lens.toContext, Context.Lens.lift,
      firstChallengeStmtLens, OracleStatement.Lens.lift, fcRelOut, Set.mem_setOf_eq]
    exact hRelIn

end Spartan.Spec
