/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G198MobiusIncidenceNormalForm

/-!
# G199: multiplicative normalization of the depth-three incidence

For a nonzero multiplicatively closed finite set `G`, every fiber of `2x+z=3a` with `a ∈ G`
is obtained from the single normalized fiber `2u+v=3` by `(u,v) ↦ (au,av)`.  Consequently

`N = |G| M`,

where `N` is G198's three-variable incidence count and
`M = #{(u,v) ∈ G² : 2u+v=3}`.  Hence

`⟨B,C⟩_c = |G| (|F| M - |G|²)`.

This reduces the signed Möbius overlap to one affine intersection of two multiplicative-subgroup
translates, the surface controlled by shifted-subgroup collision estimates.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G199MultiplicativeIncidenceNormalization

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G176RepetitionDefectCovariance
open ArkLib.ProximityGap.Frontier.G192DepthThreeSymmetricPatterns
open ArkLib.ProximityGap.Frontier.G194DepthThreeMobiusTransform
open ArkLib.ProximityGap.Frontier.G198MobiusIncidenceNormalForm

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def normalizedPairTripleFiber (G : Finset F) : Finset (F × F) :=
  (G ×ˢ G).filter fun uv => uv.1 + uv.1 + uv.2 = 1 + 1 + 1

noncomputable def affineCollisionFilter (G : Finset F) : Finset F :=
  G.filter fun u => (1 + 1 + 1) - (u + u) ∈ G

/-- The normalized two-variable equation has a unique second coordinate, so it is exactly one
affine intersection count. -/
theorem normalizedPairTripleFiber_card_eq_affineCollisionFilter (G : Finset F) :
    (normalizedPairTripleFiber G).card = (affineCollisionFilter G).card := by
  classical
  apply Finset.card_bij (fun uv _ => uv.1)
  · intro uv huv
    rw [normalizedPairTripleFiber, Finset.mem_filter, Finset.mem_product] at huv
    rw [affineCollisionFilter, Finset.mem_filter]
    refine ⟨huv.1.1, ?_⟩
    rw [show (1 + 1 + 1) - (uv.1 + uv.1) = uv.2 by
      calc
        _ = (uv.1 + uv.1 + uv.2) - (uv.1 + uv.1) := by rw [huv.2]
        _ = uv.2 := by ring]
    exact huv.1.2
  · intro uv huv wz hwz heq
    rw [normalizedPairTripleFiber, Finset.mem_filter] at huv hwz
    apply Prod.ext
    · exact heq
    · calc
        uv.2 = (1 + 1 + 1) - (uv.1 + uv.1) := by
          rw [← huv.2]
          ring
        _ = (1 + 1 + 1) - (wz.1 + wz.1) := by rw [heq]
        _ = wz.2 := by
          rw [← hwz.2]
          ring
  · intro u hu
    let v := (1 + 1 + 1) - (u + u)
    refine ⟨(u, v), ?_, rfl⟩
    rw [affineCollisionFilter, Finset.mem_filter] at hu
    rw [normalizedPairTripleFiber, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hu.1, hu.2⟩, by simp [v]⟩

theorem pairTripleIncidenceCount_eq_sum_pair_fibers (G : Finset F) :
    pairTripleIncidenceCount G =
      ∑ a ∈ G, (pairParamFiber G (a + a + a)).card := by
  classical
  unfold pairTripleIncidenceCount
  have hmaps : ∀ a ∈ G, a + a + a ∈ (Finset.univ : Finset F) := by simp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [tripleParamFiber]
  symm
  calc
    _ = ∑ _i ∈ G.filter (fun i => i + i + i = t), (pairParamFiber G t).card := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [hi.2]
    _ = (G.filter (fun i => i + i + i = t)).card * (pairParamFiber G t).card := by
      simp
    _ = _ := Nat.mul_comm _ _

theorem pairParamFiber_three_card_eq_normalized
    (G : Finset F) (hclosed : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    {a : F} (ha : a ∈ G) (ha0 : a ≠ 0) (hainv : a⁻¹ ∈ G) :
    (pairParamFiber G (a + a + a)).card = (normalizedPairTripleFiber G).card := by
  classical
  apply Finset.card_bij (fun xz _ => (xz.1 * a⁻¹, xz.2 * a⁻¹))
  · intro xz hxz
    rw [pairParamFiber, Finset.mem_filter, Finset.mem_product] at hxz
    rw [normalizedPairTripleFiber, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hclosed xz.1 hxz.1.1 a⁻¹ hainv,
      hclosed xz.2 hxz.1.2 a⁻¹ hainv⟩, ?_⟩
    calc
      xz.1 * a⁻¹ + xz.1 * a⁻¹ + xz.2 * a⁻¹ =
          (xz.1 + xz.1 + xz.2) * a⁻¹ := by ring
      _ = (a + a + a) * a⁻¹ := by rw [hxz.2]
      _ = 1 + 1 + 1 := by field_simp
  · intro xz hxz yz hyz heq
    apply Prod.ext
    · have h := congrArg Prod.fst heq
      exact mul_right_cancel₀ (inv_ne_zero ha0) h
    · have h := congrArg Prod.snd heq
      exact mul_right_cancel₀ (inv_ne_zero ha0) h
  · intro uv huv
    refine ⟨(a * uv.1, a * uv.2), ?_, ?_⟩
    · rw [normalizedPairTripleFiber, Finset.mem_filter, Finset.mem_product] at huv
      rw [pairParamFiber, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨hclosed a ha uv.1 huv.1.1, hclosed a ha uv.2 huv.1.2⟩, ?_⟩
      calc
        a * uv.1 + a * uv.1 + a * uv.2 = a * (uv.1 + uv.1 + uv.2) := by ring
        _ = a * (1 + 1 + 1) := by rw [huv.2]
        _ = a + a + a := by ring
    · apply Prod.ext
      · change a * uv.1 * a⁻¹ = uv.1
        calc
          a * uv.1 * a⁻¹ = (a * a⁻¹) * uv.1 := by ring
          _ = uv.1 := by rw [mul_inv_cancel₀ ha0, one_mul]
      · change a * uv.2 * a⁻¹ = uv.2
        calc
          a * uv.2 * a⁻¹ = (a * a⁻¹) * uv.2 := by ring
          _ = uv.2 := by rw [mul_inv_cancel₀ ha0, one_mul]

/-- **Multiplicative factorization of G198's incidence count.** -/
theorem pairTripleIncidenceCount_eq_card_mul_normalized
    (G : Finset F) (hclosed : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (hnonzero : ∀ a ∈ G, a ≠ 0) (hinv : ∀ a ∈ G, a⁻¹ ∈ G) :
    pairTripleIncidenceCount G = G.card * (normalizedPairTripleFiber G).card := by
  rw [pairTripleIncidenceCount_eq_sum_pair_fibers]
  calc
    _ = ∑ _a ∈ G, (normalizedPairTripleFiber G).card := by
      apply Finset.sum_congr rfl
      intro a ha
      exact pairParamFiber_three_card_eq_normalized G hclosed ha (hnonzero a ha) (hinv a ha)
    _ = G.card * (normalizedPairTripleFiber G).card := by simp

/-- **Covariance reduced to one normalized affine subgroup collision.** -/
theorem pair_triple_centeredInner_eq_normalized
    (G : Finset F) (hclosed : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (hnonzero : ∀ a ∈ G, a ≠ 0) (hinv : ∀ a ∈ G, a⁻¹ ∈ G) :
    centeredInner (pair01Profile G) (allThreeEqualProfile G) =
      (G.card : ℝ) *
        ((Fintype.card F : ℝ) * (normalizedPairTripleFiber G).card - G.card ^ 2) := by
  rw [pair_triple_centeredInner_eq_incidence_discrepancy,
    pairTripleIncidenceCount_eq_card_mul_normalized G hclosed hnonzero hinv]
  push_cast
  ring

/-- Final affine-collision form of the signed overlap. -/
theorem pair_triple_centeredInner_eq_affine_collision
    (G : Finset F) (hclosed : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (hnonzero : ∀ a ∈ G, a ≠ 0) (hinv : ∀ a ∈ G, a⁻¹ ∈ G) :
    centeredInner (pair01Profile G) (allThreeEqualProfile G) =
      (G.card : ℝ) *
        ((Fintype.card F : ℝ) * (affineCollisionFilter G).card - G.card ^ 2) := by
  rw [pair_triple_centeredInner_eq_normalized G hclosed hnonzero hinv,
    normalizedPairTripleFiber_card_eq_affineCollisionFilter]

#print axioms normalizedPairTripleFiber_card_eq_affineCollisionFilter
#print axioms pairTripleIncidenceCount_eq_sum_pair_fibers
#print axioms pairParamFiber_three_card_eq_normalized
#print axioms pairTripleIncidenceCount_eq_card_mul_normalized
#print axioms pair_triple_centeredInner_eq_normalized
#print axioms pair_triple_centeredInner_eq_affine_collision

end ArkLib.ProximityGap.Frontier.G199MultiplicativeIncidenceNormalization
