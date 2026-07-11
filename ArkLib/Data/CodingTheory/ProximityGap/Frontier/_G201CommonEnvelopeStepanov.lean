/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G200CoefficientAbsorptionStepanov

/-!
# G201: common-envelope Stepanov reduction for arbitrary coefficient cosets

G200 applies the existing one-subgroup Stepanov bound when `2,-1 ∈ G`.  Without coefficient
absorption, choose any common envelope `H` containing both coefficient cosets `2G` and `-G`.
The injection

`u ↦ x=2u`

sends `u ∈ G`, `3-2u ∈ G` into `x ∈ H`, `x-3 ∈ H`.  Therefore G199's affine count
is bounded by one standard shifted collision in `H`, and G103F applies with the exponent of `H`.

This theorem makes the exact price of avoiding the two-coset generalization visible: enlargement
from `G` to a common root-of-unity envelope `H`.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G201CommonEnvelopeStepanov

open ArkLib.ProximityGap.Frontier.G176RepetitionDefectCovariance
open ArkLib.ProximityGap.Frontier.G199MultiplicativeIncidenceNormalization
open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Common-envelope injection.** No multiplicative closure is needed for this combinatorial
step; only containment of the two coefficient images. -/
theorem affineCollisionFilter_card_le_envelope_shift
    (G H : Finset F) (htwo0 : (1 + 1 : F) ≠ 0)
    (htwo : ∀ u ∈ G, (1 + 1) * u ∈ H)
    (hneg : ∀ v ∈ G, (-1 : F) * v ∈ H) :
    (affineCollisionFilter G).card ≤
      (H.filter fun x => x - (1 + 1 + 1) ∈ H).card := by
  classical
  apply Finset.card_le_card_of_injOn (f := fun u => (1 + 1) * u)
  · intro u hu
    change u ∈ affineCollisionFilter G at hu
    change (1 + 1) * u ∈ H.filter (fun x => x - (1 + 1 + 1) ∈ H)
    rw [affineCollisionFilter, Finset.mem_filter] at hu
    rw [Finset.mem_filter]
    refine ⟨htwo u hu.1, ?_⟩
    convert hneg ((1 + 1 + 1) - (u + u)) hu.2 using 1 <;> ring
  · intro u hu v hv huv
    exact mul_left_cancel₀ htwo0 huv

variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-- **General one-envelope Stepanov consumer.** The exponent `t` is that of `H`, not necessarily
that of `G`; this is the exact enlargement overhead. -/
theorem affineCollisionFilter_card_le_four_sq_of_envelope
    (G H : Finset (ZMod p)) (htwo0 : (1 + 1 : ZMod p) ≠ 0)
    (htwo : ∀ u ∈ G, (1 + 1) * u ∈ H)
    (hneg : ∀ v ∈ G, (-1 : ZMod p) * v ∈ H)
    {t B : ℕ} (hB : 2 ≤ B) (h2B : 2 * B ≤ t) (hB3 : 2 * t ≤ B ^ 3)
    (hp : t * B ≤ p) (hpow : ∀ x ∈ H, x ^ t = 1)
    (hthree : (1 + 1 + 1 : ZMod p) ≠ 0) :
    (affineCollisionFilter G).card ≤ 4 * B ^ 2 := by
  exact (affineCollisionFilter_card_le_envelope_shift G H htwo0 htwo hneg).trans
    (card_collision_le_four_sq H hB h2B hB3 hp hpow hthree)

/-- A direct covariance upper bound from any affine-collision cardinality bound. -/
theorem pair_triple_centeredInner_le_of_affineCollisionFilter_card_le
    (G : Finset F) (hclosed : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (hnonzero : ∀ a ∈ G, a ≠ 0) (hinv : ∀ a ∈ G, a⁻¹ ∈ G)
    (K : ℕ) (hK : (affineCollisionFilter G).card ≤ K) :
    centeredInner
        (ArkLib.ProximityGap.Frontier.G194DepthThreeMobiusTransform.pair01Profile G)
        (ArkLib.ProximityGap.Frontier.G192DepthThreeSymmetricPatterns.allThreeEqualProfile G) ≤
      (G.card : ℝ) * ((Fintype.card F : ℝ) * K - G.card ^ 2) := by
  rw [pair_triple_centeredInner_eq_affine_collision G hclosed hnonzero hinv]
  have hcard : ((affineCollisionFilter G).card : ℝ) ≤ K := by exact_mod_cast hK
  have hn : (0 : ℝ) ≤ G.card := by positivity
  have hq : (0 : ℝ) ≤ Fintype.card F := by positivity
  apply mul_le_mul_of_nonneg_left _ hn
  have hmul := mul_le_mul_of_nonneg_left hcard hq
  linarith

/-- **Composed common-envelope covariance bound.** -/
theorem pair_triple_centeredInner_le_of_envelope_stepanov
    (G H : Finset (ZMod p))
    (hclosed : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (hnonzero : ∀ a ∈ G, a ≠ 0) (hinv : ∀ a ∈ G, a⁻¹ ∈ G)
    (htwo0 : (1 + 1 : ZMod p) ≠ 0)
    (htwo : ∀ u ∈ G, (1 + 1) * u ∈ H)
    (hneg : ∀ v ∈ G, (-1 : ZMod p) * v ∈ H)
    {t B : ℕ} (hB : 2 ≤ B) (h2B : 2 * B ≤ t) (hB3 : 2 * t ≤ B ^ 3)
    (hp : t * B ≤ p) (hpow : ∀ x ∈ H, x ^ t = 1)
    (hthree : (1 + 1 + 1 : ZMod p) ≠ 0) :
    centeredInner
        (ArkLib.ProximityGap.Frontier.G194DepthThreeMobiusTransform.pair01Profile G)
        (ArkLib.ProximityGap.Frontier.G192DepthThreeSymmetricPatterns.allThreeEqualProfile G) ≤
      (G.card : ℝ) * ((p : ℝ) * (4 * B ^ 2 : ℕ) - G.card ^ 2) := by
  have hM := affineCollisionFilter_card_le_four_sq_of_envelope
    G H htwo0 htwo hneg hB h2B hB3 hp hpow hthree
  have hcov := pair_triple_centeredInner_le_of_affineCollisionFilter_card_le
    G hclosed hnonzero hinv (4 * B ^ 2) hM
  simpa using hcov

#print axioms affineCollisionFilter_card_le_envelope_shift
#print axioms affineCollisionFilter_card_le_four_sq_of_envelope
#print axioms pair_triple_centeredInner_le_of_affineCollisionFilter_card_le
#print axioms pair_triple_centeredInner_le_of_envelope_stepanov

end ArkLib.ProximityGap.Frontier.G201CommonEnvelopeStepanov
