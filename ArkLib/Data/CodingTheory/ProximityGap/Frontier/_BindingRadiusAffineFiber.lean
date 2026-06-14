/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

set_option linter.unusedSectionVars false

/-!
# Binding-radius affine fibres (#407)

The latest #407 binding-radius reframe isolates a different object from the
Gaussian-period/BGK sup-norm proxy.  At a fixed witness set, explainability of the
line `u₀ + γ u₁` is affine in the single scalar `γ`.  When the witness is
over-determined and at least one affine direction coefficient is nonzero, that
witness contributes **at most one** scalar; with two nonzero constraints, their
residual ratios must agree.

This file packages only that finite-field counting mechanism.  It does not claim
monomial extremality, p-independence for all `n`, or closure of #407.  It gives
the Lean-side gate needed by the binding-radius path:

* a non-heavy affine slot pins `γ = -A/B`;
* two non-heavy slots force equal pinned ratios;
* any bad-scalar predicate whose witnesses impose such affine constraints injects
  into the active witness family.

The last theorem is the formal version of "count consistent binding witnesses,
not a p-dependent BGK proxy" at the purely affine layer.
-/

open Finset

namespace ProximityGap.Frontier.BindingRadiusAffineFiber

variable {F Ω J : Type*}

/-- One affine scalar constraint: `A + γ B = 0`.  In the binding-radius
application, `A` is the residual of `u₀` on a witness subtuple and `B` is the
corresponding residual of `u₁`. -/
def affineConstraint [Add F] [Mul F] [Zero F] (A B γ : F) : Prop :=
  A + γ * B = 0

variable [Field F]

/-- A non-heavy affine slot pins the scalar to the residual ratio `-A / B`. -/
theorem affineConstraint_eq_neg_div {A B γ : F} (hB : B ≠ 0)
    (h : affineConstraint A B γ) :
    γ = -A / B := by
  unfold affineConstraint at h
  have hmul : γ * B = -A := by
    have h' : γ * B + A = 0 := by
      rw [add_comm]
      exact h
    exact eq_neg_of_add_eq_zero_left h'
  calc
    γ = γ * B / B := by field_simp [hB]
    _ = -A / B := by rw [hmul]

/-- Two non-heavy affine slots on the same scalar must have the same pinned ratio.
This is the over-determined consistency test: if two residual equations in the
single variable `γ` both hold, their `-A/B` values are forced to agree. -/
theorem ratio_eq_of_two_affine_constraints {A₁ B₁ A₂ B₂ γ : F}
    (hB₁ : B₁ ≠ 0) (hB₂ : B₂ ≠ 0)
    (h₁ : affineConstraint A₁ B₁ γ)
    (h₂ : affineConstraint A₂ B₂ γ) :
    -A₁ / B₁ = -A₂ / B₂ := by
  have hγ₁ := affineConstraint_eq_neg_div hB₁ h₁
  have hγ₂ := affineConstraint_eq_neg_div hB₂ h₂
  rw [← hγ₁, ← hγ₂]

section Counting

variable [Fintype F] [DecidableEq F]
variable [Fintype Ω] [Inhabited Ω]
variable [Fintype J]

open Classical in
/-- Witnesses with at least one moving affine slot.  Heavy witnesses, where all
direction coefficients vanish, are deliberately excluded: they are exactly the
saturation/whole-field branch that must be handled separately. -/
noncomputable def activeWitnesses (B : Ω → J → F) : Finset Ω :=
  Finset.univ.filter fun ω => ∃ j : J, B ω j ≠ 0

omit [Fintype F] [Inhabited Ω] in
open Classical in
/-- Membership in the active-witness family. -/
theorem mem_activeWitnesses {B : Ω → J → F} {ω : Ω} :
    ω ∈ activeWitnesses B ↔ ∃ j : J, B ω j ≠ 0 := by
  simp [activeWitnesses]

open Classical in
/-- **Affine-fibre counting gate.**

Let `P γ` be any bad-scalar predicate.  Suppose each bad scalar chooses a witness
`owner γ`, each chosen witness has a nonzero affine slot `j0 γ`, and the scalar
`γ` satisfies every affine constraint carried by that witness.  Then the bad
scalars inject into the active witness family.

In #407 terms: after the far-coset/binding-radius reduction has produced affine
residual equations on a witness, this theorem is the no-BGK counting step.  Any
remaining difficulty is in characterizing/counting the active **consistent**
witnesses and in excluding the heavy/saturation branch, not in a character-sum
sup-norm estimate. -/
theorem badScalar_card_le_activeWitnesses
    (P : F → Prop) [DecidablePred P]
    (A B : Ω → J → F)
    (owner : ∀ γ : F, P γ → Ω)
    (j0 : ∀ γ : F, ∀ _hγ : P γ, J)
    (hj0 : ∀ γ hγ, B (owner γ hγ) (j0 γ hγ) ≠ 0)
    (hconstraints : ∀ γ hγ, ∀ j : J,
      affineConstraint (A (owner γ hγ) j) (B (owner γ hγ) j) γ) :
    (Finset.univ.filter fun γ : F => P γ).card ≤ (activeWitnesses B).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun γ => if hγ : P γ then owner γ hγ else default) ?maps ?inj
  · intro γ hγ
    have hPγ : P γ := (Finset.mem_filter.mp hγ).2
    change (if h : P γ then owner γ h else default) ∈ activeWitnesses B
    simp only [hPγ, dite_true]
    rw [mem_activeWitnesses]
    exact ⟨j0 γ hPγ, by simpa using hj0 γ hPγ⟩
  · intro γ hγ γ' hγ' howner
    have hPγ : P γ := (Finset.mem_filter.mp hγ).2
    have hPγ' : P γ' := (Finset.mem_filter.mp hγ').2
    have howner' : owner γ hPγ = owner γ' hPγ' := by
      simpa [hPγ, hPγ'] using howner
    let j := j0 γ hPγ
    have hB : B (owner γ hPγ) j ≠ 0 := hj0 γ hPγ
    have hγratio :
        γ = -A (owner γ hPγ) j / B (owner γ hPγ) j :=
      affineConstraint_eq_neg_div hB (hconstraints γ hPγ j)
    have hγ'ratio :
        γ' = -A (owner γ hPγ) j / B (owner γ hPγ) j := by
      have hc := hconstraints γ' hPγ' j
      rw [← howner'] at hc
      exact affineConstraint_eq_neg_div hB hc
    rw [hγratio, hγ'ratio]

end Counting

end ProximityGap.Frontier.BindingRadiusAffineFiber

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.BindingRadiusAffineFiber.affineConstraint_eq_neg_div
#print axioms ProximityGap.Frontier.BindingRadiusAffineFiber.ratio_eq_of_two_affine_constraints
#print axioms ProximityGap.Frontier.BindingRadiusAffineFiber.badScalar_card_le_activeWitnesses
