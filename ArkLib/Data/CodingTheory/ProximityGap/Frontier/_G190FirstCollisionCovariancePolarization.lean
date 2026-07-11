/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G189DisjointFirstCollisionPartition

/-!
# G190: exact covariance polarization of first-collision strata

G189 removes combinatorial overlap by partitioning repeated tuples into disjoint first-collision
strata.  Their target-sum profiles can still overlap.  This file expands the centered mass exactly:

`V(sum_i P_i) = sum_i V(P_i) + sum_{i != j} <P_i,P_j>_c`.

Thus the remaining certificate needed to avoid the Cauchy factor is precisely an upper bound on
the aggregate off-diagonal centered covariance.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G190FirstCollisionCovariancePolarization

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
open ArkLib.ProximityGap.Frontier.G176RepetitionDefectCovariance
open ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
open ArkLib.ProximityGap.Frontier.G183PairCollisionEnergyReduction
open ArkLib.ProximityGap.Frontier.G189DisjointFirstCollisionPartition

def profileSum {I A : Type*} [DecidableEq I]
    (S : Finset I) (p : I → A → ℝ) : A → ℝ :=
  fun a => ∑ i ∈ S, p i a

theorem centeredInner_profileSum_left {I A : Type*} [DecidableEq I] [Fintype A]
    (S : Finset I) (p : I → A → ℝ) (g : A → ℝ) :
    centeredInner (profileSum S p) g = ∑ i ∈ S, centeredInner (p i) g := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [profileSum, centeredInner]
  | @insert i S hi ih =>
      rw [show profileSum (insert i S) p = fun a => p i a + profileSum S p a by
        funext a
        simp [profileSum, hi]]
      rw [centeredInner_add_left, ih]
      simp [hi]

theorem centeredInner_profileSum_right {I A : Type*} [DecidableEq I] [Fintype A]
    (f : A → ℝ) (S : Finset I) (p : I → A → ℝ) :
    centeredInner f (profileSum S p) = ∑ i ∈ S, centeredInner f (p i) := by
  rw [centeredInner_comm, centeredInner_profileSum_left]
  apply Finset.sum_congr rfl
  intro i hi
  exact centeredInner_comm _ _

/-- **Finite-profile centered polarization.** -/
theorem centeredSqMass_profileSum {I A : Type*} [DecidableEq I] [Fintype A]
    (S : Finset I) (p : I → A → ℝ) :
    centeredSqMass (profileSum S p) =
      ∑ i ∈ S, centeredSqMass (p i) +
        ∑ ij ∈ S.offDiag, centeredInner (p ij.1) (p ij.2) := by
  rw [centeredSqMass_eq_inner, centeredInner_profileSum_left]
  simp_rw [centeredInner_profileSum_right]
  rw [← Finset.sum_product', ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag S), Finset.sum_diag]
  simp_rw [← centeredSqMass_eq_inner]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def firstCollisionAggregateCovariance
    (G : Finset F) {r : ℕ} (hr : 2 ≤ r) : ℝ :=
  ∑ ijkl ∈ (collisionIndices r).offDiag,
    centeredInner (firstCollisionProfile G hr ijkl.1)
      (firstCollisionProfile G hr ijkl.2)

theorem factorialRepetitionDefect_eq_profileSum
    (G : Finset F) {r : ℕ} (hr : 2 ≤ r) :
    factorialRepetitionDefect G r =
      profileSum (collisionIndices r) (firstCollisionProfile G hr) := by
  funext t
  exact factorialRepetitionDefect_eq_sum_firstCollisionProfile G hr t

/-- **Exact first-collision covariance identity.** -/
theorem factorialRepetitionDefect_centeredMass_eq_strata_add_covariance
    (G : Finset F) {r : ℕ} (hr : 2 ≤ r) :
    centeredSqMass (factorialRepetitionDefect G r) =
      ∑ ij ∈ collisionIndices r, centeredSqMass (firstCollisionProfile G hr ij) +
        firstCollisionAggregateCovariance G hr := by
  rw [factorialRepetitionDefect_eq_profileSum]
  exact centeredSqMass_profileSum _ _

/-- If the aggregate off-diagonal covariance is nonpositive, the disjoint-stratum decomposition
removes the entire Cauchy factor. -/
theorem factorialRepetitionDefect_centeredMass_le_sum_strata_of_covariance_nonpos
    (G : Finset F) {r : ℕ} (hr : 2 ≤ r)
    (hcov : firstCollisionAggregateCovariance G hr ≤ 0) :
    centeredSqMass (factorialRepetitionDefect G r) ≤
      ∑ ij ∈ collisionIndices r, centeredSqMass (firstCollisionProfile G hr ij) := by
  rw [factorialRepetitionDefect_centeredMass_eq_strata_add_covariance G hr]
  linarith

#print axioms centeredSqMass_profileSum
#print axioms factorialRepetitionDefect_centeredMass_eq_strata_add_covariance
#print axioms factorialRepetitionDefect_centeredMass_le_sum_strata_of_covariance_nonpos

end ArkLib.ProximityGap.Frontier.G190FirstCollisionCovariancePolarization
