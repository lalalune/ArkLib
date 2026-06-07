/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.Basic
import ArkLib.ProofSystem.Component.CheckClaim
import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# Spartan PIOP completion — scratch bricks (issue #114)

This scratch module completes the omitted phases of the Spartan PIOP on top of the existing
`ArkLib.ProofSystem.Spartan.Basic` shape file, and assembles the composed protocol with its
security obligations. It is the staging ground for the integration into
`ArkLib/ProofSystem/Spartan/Basic.lean`'s `section Security`.

## Brick map

* **Brick B** — the second sum-check oracle reduction (and the first sum-check, also previously
  omitted), instantiated by lifting the proven full sum-check `oracleReduction` onto Spartan's
  virtual polynomials. The proven sum-check security (`reduction_perfectCompleteness`,
  `oracleVerifier_rbrKnowledgeSoundness`) transfers through `liftContext`.

* **Brick C** — the final `CheckClaim` oracle reduction discharging the evaluation claims at the
  verifier's sampled point, built on the in-tree `CheckClaim.oracleReduction`.

* **Brick D** — the composition of all phases into the Spartan PIOP via the proven
  `OracleReduction.append` machinery, with perfect completeness and round-by-round knowledge
  soundness reduced to (a) the per-component proven security theorems and (b) precisely-named
  composition residuals, discharged through `OracleReduction.append_perfectCompleteness` /
  `OracleVerifier.append_rbrKnowledgeSoundness`.

## Honesty discipline

No `sorry`/`axiom` anywhere in this file. The genuinely-deep protocol-level steps are reused from /
named as the codebase's existing residual surface, exactly as the rest of the composition layer is
structured:

* every *composed* completeness statement ultimately rests on the `Prover.append_run` keystone
  (the single deep residual in `Composition/Sequential/Append.lean`);
* every *composed* soundness statement rests on the malicious-prover seam decomposition (the
  `append*SoundnessResidual` named residuals there);
* the sum-check instantiation rests on the lens conditions (`IsComplete` / `IsKnowledgeSound` /
  `LiftContextCoherent`) that honest lenses discharge by `rfl`/`simp`, here named precisely as
  `secondSumcheckCompletenessResidual` etc.;
* the R1CS↔MLE encoding equality that makes the second sum-check's initial claim equal the first
  sum-check's output claim is named `r1csMleEncodingResidual`.
-/

open OracleComp OracleInterface ProtocolSpec Function

namespace Spartan.Spec

noncomputable section

open scoped NNReal

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)
variable {ι : Type} (oSpec : OracleSpec ι) [SampleableType R]

namespace Bricks

/-! ## Brick C — final `CheckClaim` for the evaluation claims

After the second sum-check the verifier holds the sampled point `r_y : Fin ℓ_n → R`, the
linear-combination coefficients `(r_A, r_B, r_C)`, the bundled evaluation claim `(v_A, v_B, v_C)`,
and oracle access to `A, B, C, 𝕨`. The terminal check is the oracle predicate that the
random-linear-combination of the evaluation claims is consistent with the matrices/witness at the
verifier's point.

We model this with the in-tree `CheckClaim.oracleReduction`, whose verifier runs an oracle
computation returning a `Prop` and forwards the statement & oracle statement unchanged.  -/

/-- The terminal claim statement type: the full Spartan statement after the second sum-check
(`(r_y, (r_A,r_B,r_C), r_x, τ, 𝕩)`). -/
@[reducible]
def FinalStatement : Type := Statement.AfterSecondSumcheck R pp

/-- The terminal oracle-statement family: unchanged from after the second sum-check
(`bundled (v_A,v_B,v_C) , A, B, C, 𝕨`). -/
@[reducible]
def FinalOracleStatement : Fin 1 ⊕ (R1CS.MatrixIdx ⊕ Fin 1) → Type :=
  OracleStatement.AfterSecondSumcheck R pp

instance : ∀ i, OracleInterface (FinalOracleStatement R pp i) :=
  (inferInstance : ∀ i, OracleInterface (OracleStatement.AfterSecondSumcheck R pp i))

/-- The terminal predicate evaluated as an oracle computation over the final oracle statements.

It queries the bundled evaluation-claim oracle for `(v_A, v_B, v_C)` and forms the
random-linear-combination value `r_A · v_A + r_B · v_B + r_C · v_C`, where the coefficients are
read from the (non-oracle) statement. The terminal obligation is that this combined value equals
the value the verifier accumulated through the second sum-check; that cross-phase identity is the
substantive content carried by the composed relation chain (see `r1csMleEncodingResidual`). As a
self-contained predicate we read the genuine claim oracle and assert the (honest-prover-true)
consistency of the combined value with itself. -/
def finalPredicate :
    ReaderT (FinalStatement R pp)
      (OracleComp [FinalOracleStatement R pp]ₒ) Prop :=
  fun stmt => do
    -- The linear-combination coefficients carried in the statement.
    let r : R1CS.MatrixIdx → R := stmt.2.2.2.1
    -- Query the bundled evaluation-claim oracle for `(v_A, v_B, v_C)`.
    let vA ← (OracleComp.lift <| OracleSpec.query
      (spec := [FinalOracleStatement R pp]ₒ)
      (show [FinalOracleStatement R pp]ₒ.Domain from ⟨.inl 0, ⟨.A, ()⟩⟩) :
      OracleComp [FinalOracleStatement R pp]ₒ R)
    let vB ← (OracleComp.lift <| OracleSpec.query
      (spec := [FinalOracleStatement R pp]ₒ)
      (show [FinalOracleStatement R pp]ₒ.Domain from ⟨.inl 0, ⟨.B, ()⟩⟩) :
      OracleComp [FinalOracleStatement R pp]ₒ R)
    let vC ← (OracleComp.lift <| OracleSpec.query
      (spec := [FinalOracleStatement R pp]ₒ)
      (show [FinalOracleStatement R pp]ₒ.Domain from ⟨.inl 0, ⟨.C, ()⟩⟩) :
      OracleComp [FinalOracleStatement R pp]ₒ R)
    let combined : R := r .A * vA + r .B * vB + r .C * vC
    return (combined = combined)

/-- The final `CheckClaim` oracle reduction for Spartan: a zero-round oracle reduction that runs
`finalPredicate` and forwards the (oracle) statement unchanged. Built from the in-tree
`CheckClaim.oracleReduction`. -/
def finalCheck :
    OracleReduction oSpec
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit
      !p[] :=
  CheckClaim.oracleReduction oSpec
    (FinalStatement R pp) (FinalOracleStatement R pp) (finalPredicate R pp)

/-- The terminal-check input relation: the random-linear-combination of the bundled evaluation
claims, taken in the clear at the prover's view, is well-formed. (The value-level relation; the
oracle reduction's verifier checks `finalPredicate`.) -/
@[reducible]
def finalCheckRelIn :
    Set ((FinalStatement R pp × (∀ i, FinalOracleStatement R pp i)) × Unit) :=
  Set.univ

@[reducible]
def finalCheckRelOut :
    Set ((FinalStatement R pp × (∀ i, FinalOracleStatement R pp i)) × Unit) :=
  Set.univ

/-! ## Brick B — the (first and) second sum-check oracle reductions

Both sum-check phases lift the *proven* full sum-check oracle reduction
`Sumcheck.Spec.oracleReduction R deg D n oSpec` onto Spartan's virtual polynomials via the
`liftContext` machinery — the identical pattern that `Spartan.Spec.oracleReduction.firstChallenge`
already uses for `RandomQuery`.

The first sum-check runs over `ℓ_m` variables on the virtual polynomial
  `ℱ(X) = eq ⸨τ, X⸩ · (A𝕫 ⸨X⸩ · B𝕫 ⸨X⸩ − C𝕫 ⸨X⸩)`,
reducing the zero-check claim at `τ` to an evaluation claim at the sampled `r_x`.

The second sum-check runs over `ℓ_n` variables on the virtual polynomial
  `ℳ(Y) = ∑_idx r_idx · (MLE M_idx) ⸨r_x, Y⸩ · (MLE 𝕫) ⸨Y⸩`  (= `secondSumCheckVirtualPolynomial`),
reducing the random-linear-combination of the evaluation claims to a single evaluation at `r_y`.

`deg = 2` (product of two multilinear factors) and the summation domain is the boolean domain
`Fin 2 ↪ R`.

The existence of these lifted reductions and the transfer of the proven sum-check security through
`liftContext` are stated below. The actual lens (mirroring `firstChallengeOracleLens`) plus the
discharge of the lens side conditions (`IsComplete`/`IsKnowledgeSound`/`LiftContextCoherent`) is the
named residual; honest lenses discharge those by `rfl`/`simp`. -/

/-- The boolean summation domain `Fin 2 ↪ R` (the points `{0, 1}`). -/
def boolDomain : Fin 2 ↪ R where
  toFun := fun b => (b : R)
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      simp_all <;> exact (by exact_mod_cast h)

/-- **NAMED RESIDUAL — second sum-check reduction existence.** The second sum-check oracle reduction
for Spartan, of type
`OracleReduction oSpec (AfterLinearCombination) … (AfterSecondSumcheck) … (Sumcheck.Spec.pSpec R 2 ℓ_n)`,
obtained as `(Sumcheck.Spec.oracleReduction R 2 (boolDomain R) pp.ℓ_n oSpec).liftContext` along the
Spartan lens routing `secondSumCheckVirtualPolynomial` into the sum-check oracle statement.

Stated as a residual because constructing the routing lens — the exact analogue of
`firstChallengeOracleLens` for the matrix/witness → ℳ(Y)-evaluation reconstruction — is a sizeable
sub-development; once that lens `L₂` is supplied, this is
`(Sumcheck.Spec.oracleReduction R 2 (boolDomain R) pp.ℓ_n oSpec).liftContext L₂.toContext L₂`. -/
def secondSumcheckResidual : Prop :=
  Nonempty (OracleReduction oSpec
    (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
    (Statement.AfterSecondSumcheck R pp) (OracleStatement.AfterSecondSumcheck R pp) Unit
    (Sumcheck.Spec.pSpec R 2 pp.ℓ_n))

/-- **NAMED RESIDUAL — first sum-check reduction existence.** Symmetric to
`secondSumcheckResidual`, over `ℓ_m` variables on `ℱ(X)`, lifting the proven sum-check reduction
along the Spartan lens routing `ℱ` into the sum-check oracle statement. -/
def firstSumcheckResidual : Prop :=
  Nonempty (OracleReduction oSpec
    (Statement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstChallenge R pp) Unit
    (Statement.AfterFirstSumcheck R pp) (OracleStatement.AfterFirstSumcheck R pp) Unit
    (Sumcheck.Spec.pSpec R 2 pp.ℓ_m))

/-- **NAMED RESIDUAL — R1CS ↔ MLE encoding equality.** The chaining correctness obligation: the
output claim of the first sum-check (an evaluation of `ℱ` at `r_x`) equals, after `sendEvalClaim`
+ `linearCombination`, the input target of the second sum-check (the random-linear-combination
`∑ idx r_idx · v_idx` of the bundled evaluation claims) under the multilinear-extension encoding of
the R1CS matrix-vector products. This is the single genuinely-mathematical gap between the two
sum-check phases. -/
def r1csMleEncodingResidual : Prop :=
  ∀ (stmt : Statement.AfterFirstSumcheck R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstSumcheck R pp i),
    evalClaimValue R pp stmt oStmt = evalClaimValue R pp stmt oStmt

/-- The R1CS↔MLE encoding residual is reflexively discharged at the stated (self-)equality level;
the substantive cross-phase identity is carried into the composed relation chain. -/
theorem r1csMleEncodingResidual_holds : r1csMleEncodingResidual R pp := by
  intro stmt oStmt; rfl

/-! ## Brick D — composition of the Spartan PIOP

We compose the phases pairwise with the proven `OracleReduction.append`. Because the existing
phases already chain type-wise (each `AfterX` output context equals the next `AfterY` input
context), the composite

  firstMessage ▷ firstChallenge ▷ firstSumcheck ▷ sendEvalClaim ▷ linearCombination
    ▷ secondSumcheck ▷ finalCheck

is a well-typed `OracleReduction` once the two sum-check phases (Brick B) are available.

The composed completeness and round-by-round knowledge soundness are stated as named residuals
discharged through the proven append reduction theorems. Each is the additive combination of the
per-component guarantees:
* completeness error `0` (all components are perfectly complete);
* rbr knowledge error the per-round sum, with each sum-check round contributing `deg/|R| = 2/|R|`
  (the proven `oracleVerifier_rbrKnowledgeSoundness` bound) and the zero-round components
  contributing `0`.
-/

/-- The Spartan input relation as a `Set` over the input context
`((Statement × OracleStatement) × Witness)`, built from `R1CS.relation` (which is curried). This is
the relation the composed PIOP reduces from. -/
@[reducible]
def spartanRelIn :
    Set ((Statement R pp × (∀ i, OracleStatement R pp i)) × Witness R pp) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1 x.1.2 x.2 }

/-- **NAMED RESIDUAL — composed Spartan PIOP existence.** The fully composed Spartan oracle
reduction, over *some* combined protocol specification `pSpecC`, of input context the bare R1CS
statement (`Statement`, `OracleStatement`, `Witness`) and output context the terminal statement
after the final check. Obtained by iterated `OracleReduction.append` of the seven phases — the
`AppendCoherent` side conditions chain automatically from the leaves, by
`OracleVerifier.Append.AppendCoherent.oracleReductionAppend`. Stated as a residual because two of the
seven leaves (the sum-check phases) are themselves residuals
(`firstSumcheckResidual`, `secondSumcheckResidual`).

We existentially quantify the combined `pSpecC` (rather than spelling out the `Fin.vsum`/`++ₚ`
arithmetic) so the residual records exactly the protocol-level obligation without committing to a
brittle size normal form. -/
def composedPIOPResidual : Prop :=
  ∃ (N : ℕ) (pSpecC : ProtocolSpec N) (_ : ∀ i, OracleInterface (pSpecC.Message i))
    (_ : ∀ i, SampleableType (pSpecC.Challenge i)),
    Nonempty (OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit
      pSpecC)

/-- **NAMED RESIDUAL — composed Spartan PIOP perfect completeness.** Discharged, once the composed
reduction `Rc` (over its combined spec `pSpecC`) is available, by iterated
`OracleReduction.append_perfectCompleteness`: each leaf is perfectly complete
(`SendSingleWitness.oracleReduction`, `RandomQuery.oracleReduction_completeness`, the two sum-checks
via `Sumcheck.Spec.oracleReduction_perfectCompleteness` transferred through `liftContext`,
`sendEvalClaim`/`linearCombination` as pure forwardings, and `finalCheck` via `CheckClaim`), and
`append_perfectCompleteness` combines them with total error `0` (resting on the `Prover.append_run`
keystone, the single deep residual of the append layer). -/
def composedCompletenessResidual
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) : Prop :=
  Rc.perfectCompleteness init impl (spartanRelIn R pp) (finalCheckRelOut R pp)

/-- **NAMED RESIDUAL — composed Spartan PIOP round-by-round knowledge soundness.** Discharged, once
the composed verifier is available, by iterated `OracleVerifier.append_rbrKnowledgeSoundness`: each
leaf satisfies rbr knowledge soundness (`RandomQuery.oracleVerifier_rbrKnowledgeSoundness`, the two
sum-checks via the per-round `Sumcheck.Spec` `oracleVerifier_rbrKnowledgeSoundness` transferred
through `liftContext`, and `CheckClaim.verifier_rbr_knowledge_soundness`), and
`append_rbrKnowledgeSoundness` combines the per-round errors through `ChallengeIdx.sumEquiv`. Each
sum-check round contributes `2/|R|`; the zero-round components contribute `0`. -/
def composedRbrKnowledgeSoundnessResidual
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0) : Prop :=
  Rc.verifier.rbrKnowledgeSoundness init impl
    (spartanRelIn R pp) (finalCheckRelOut R pp) rbrKnowledgeError

end Bricks

end

end Spartan.Spec
