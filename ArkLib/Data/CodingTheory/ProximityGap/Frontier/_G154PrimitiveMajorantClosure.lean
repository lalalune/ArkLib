/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G153AllDepthCompositeConvolution

/-!
# G154: primitive-majorant closure and direct accident propagation

G153 expresses the full core census as primitive mass plus a convolution of smaller full censuses.
This file closes that recursion abstractly.  If `P t` bounds the primitive census and `B` is any
nonnegative convolution supersolution

`P t + Σ_{s=2}^{t-2} B s * B (t-s) ≤ B t`,

then strong induction proves `#corePairs(G,t) ≤ B t` for every `t`.

The result is then propagated directly through G145's lossless cancellation code and exact
intersection multiplicity.  This avoids the looser comparison `corePairs ≤ depthFiber`: a
primitive majorant yields an all-depth subset-accident bound, and hence a subset-sum fiber-energy
bound, with the exact binomial padding factors.

Thus the connected-packet route is reduced to constructing one explicit primitive majorant `P`
and one elementary supersolution `B`.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G154PrimitiveMajorantClosure

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G140QuantitativeAccidentDCFloor
open ArkLib.ProximityGap.Frontier.G143DepthStratifiedSubsetAccidents
open ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope
open ArkLib.ProximityGap.Frontier.G146GlobalSubsetAccidentEnvelope
open ArkLib.ProximityGap.Frontier.G152DepthFourCompositeCensus
open ArkLib.ProximityGap.Frontier.G153AllDepthCompositeConvolution

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

/-- **Primitive-majorant closure.** Any supersolution of the primitive-plus-convolution recurrence
majorizes the complete core census at every depth. -/
theorem corePairs_card_le_of_primitive_majorant
    (G : Finset F) (P B : ℕ → ℕ)
    (hprimitive : ∀ t, (primitiveCorePairs G t).card ≤ P t)
    (hsuper : ∀ t, P t +
      ∑ s ∈ Finset.Icc 2 (t - 2), B s * B (t - s) ≤ B t) :
    ∀ t, (subsetCorePairs G t).card ≤ B t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      apply (subsetCorePairs_card_le_primitive_add_convolution G t).trans
      apply (Nat.add_le_add (hprimitive t) ?_).trans (hsuper t)
      exact Finset.sum_le_sum fun s hs => by
        have hsMem := Finset.mem_Icc.mp hs
        exact Nat.mul_le_mul (ih s (by omega)) (ih (t - s) (by omega))

/-- One exact stratum is bounded directly by the core census times its intersection choices. -/
theorem stratum_card_le_corePairs_mul_choose (G : Finset F) (r t : ℕ) :
    (subsetAccidentStratum G r t).card ≤
      (subsetCorePairs G t).card * (G.card - 2 * t).choose (r - t) := by
  exact (stratum_card_le_liftCodes G r t).trans (liftCodes_card_le G r t)

/-- A full-core majorant propagates directly to the total subset-accident census. -/
theorem subsetAccidents_card_le_of_coreMajorant
    (G : Finset F) (r : ℕ) (B : ℕ → ℕ)
    (hB : ∀ t, (subsetCorePairs G t).card ≤ B t) :
    (subsetAccidents G r).card ≤
      ∑ t ∈ Finset.Icc 1 r,
        B t * (G.card - 2 * t).choose (r - t) := by
  rw [card_subsetAccidents_eq_sum_positive_strata]
  exact Finset.sum_le_sum fun t ht =>
    (stratum_card_le_corePairs_mul_choose G r t).trans
      (Nat.mul_le_mul_right _ (hB t))

/-- **G154 accident capstone.** Primitive bounds plus a convolution supersolution control every
subset-sum accident with exact intersection multiplicity. -/
theorem subsetAccidents_card_le_of_primitive_majorant
    (G : Finset F) (r : ℕ) (P B : ℕ → ℕ)
    (hprimitive : ∀ t, (primitiveCorePairs G t).card ≤ P t)
    (hsuper : ∀ t, P t +
      ∑ s ∈ Finset.Icc 2 (t - 2), B s * B (t - s) ≤ B t) :
    (subsetAccidents G r).card ≤
      ∑ t ∈ Finset.Icc 1 r,
        B t * (G.card - 2 * t).choose (r - t) := by
  exact subsetAccidents_card_le_of_coreMajorant G r B
    (corePairs_card_le_of_primitive_majorant G P B hprimitive hsuper)

/-- The same primitive majorant controls the fiber energy after adding the exact diagonal. -/
theorem subsetSum_fiberEnergy_le_of_primitive_majorant
    (G : Finset F) (r : ℕ) (P B : ℕ → ℕ)
    (hprimitive : ∀ t, (primitiveCorePairs G t).card ≤ P t)
    (hsuper : ∀ t, P t +
      ∑ s ∈ Finset.Icc 2 (t - 2), B s * B (t - s) ≤ B t) :
    fiberEnergy (subsetSumMap G r) ≤ G.card.choose r +
      ∑ t ∈ Finset.Icc 1 r,
        B t * (G.card - 2 * t).choose (r - t) := by
  rw [subsetSum_fiberEnergy_eq_choose_add_sum_strata]
  apply Nat.add_le_add_left
  exact Finset.sum_le_sum fun t ht =>
    (stratum_card_le_corePairs_mul_choose G r t).trans
      (Nat.mul_le_mul_right _
        (corePairs_card_le_of_primitive_majorant G P B hprimitive hsuper t))

#print axioms corePairs_card_le_of_primitive_majorant
#print axioms stratum_card_le_corePairs_mul_choose
#print axioms subsetAccidents_card_le_of_coreMajorant
#print axioms subsetAccidents_card_le_of_primitive_majorant
#print axioms subsetSum_fiberEnergy_le_of_primitive_majorant

end ArkLib.ProximityGap.Frontier.G154PrimitiveMajorantClosure
