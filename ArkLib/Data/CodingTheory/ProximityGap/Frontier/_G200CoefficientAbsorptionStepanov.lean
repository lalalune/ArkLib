/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G199MultiplicativeIncidenceNormalization
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G103FSubgroupCollisionBound

/-!
# G200: coefficient absorption exposes the existing Stepanov collision bound

G199 reduces the depth-three overlap to

`M = #{u ∈ G : 3 - 2u ∈ G}`.

If `2,-1 ∈ G`, multiplication by `2` bijects this affine filter with the standard shifted
collision set `{x ∈ G : x-3 ∈ G}`.  Over `ZMod p`, G103F then gives `M ≤ 4B²` under
its classical Stepanov parameter conditions.

The coefficient-membership hypotheses are explicit: this theorem does not claim they hold for
every production subgroup.  It precisely separates the already-landed one-coset case from the
remaining two-coset extension.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G200CoefficientAbsorptionStepanov

open ArkLib.ProximityGap.Frontier.G199MultiplicativeIncidenceNormalization
open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem affineCollisionFilter_card_eq_standard_shift
    (G : Finset F) (hclosed : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (hinv : ∀ x ∈ G, x⁻¹ ∈ G) (h2 : (1 + 1 : F) ∈ G)
    (hneg : (-1 : F) ∈ G) (htwo0 : (1 + 1 : F) ≠ 0) :
    (affineCollisionFilter G).card =
      (G.filter fun x => x - (1 + 1 + 1) ∈ G).card := by
  classical
  apply Finset.card_bij (fun u _ => (1 + 1) * u)
  · intro u hu
    rw [affineCollisionFilter, Finset.mem_filter] at hu
    rw [Finset.mem_filter]
    refine ⟨hclosed (1 + 1) h2 u hu.1, ?_⟩
    have hv : (1 + 1 + 1) - (u + u) ∈ G := hu.2
    have hnegv := hclosed (-1) hneg ((1 + 1 + 1) - (u + u)) hv
    convert hnegv using 1 <;> ring
  · intro u hu v hv heq
    exact mul_left_cancel₀ htwo0 heq
  · intro x hx
    rw [Finset.mem_filter] at hx
    let u := (1 + 1)⁻¹ * x
    refine ⟨u, ?_, ?_⟩
    · rw [affineCollisionFilter, Finset.mem_filter]
      have huG : u ∈ G := hclosed (1 + 1)⁻¹ (hinv (1 + 1) h2) x hx.1
      refine ⟨huG, ?_⟩
      have hnegshift := hclosed (-1) hneg (x - (1 + 1 + 1)) hx.2
      convert hnegshift using 1
      dsimp [u]
      field_simp
      ring
    · dsimp [u]
      field_simp

variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-- **G103F applies exactly when the coefficients are absorbed by the subgroup.** -/
theorem affineCollisionFilter_card_le_four_sq
    (G : Finset (ZMod p)) (hclosed : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (hinv : ∀ x ∈ G, x⁻¹ ∈ G) (h2 : (1 + 1 : ZMod p) ∈ G)
    (hneg : (-1 : ZMod p) ∈ G) (htwo0 : (1 + 1 : ZMod p) ≠ 0)
    {t B : ℕ} (hB : 2 ≤ B) (h2B : 2 * B ≤ t) (hB3 : 2 * t ≤ B ^ 3)
    (hp : t * B ≤ p) (hpow : ∀ x ∈ G, x ^ t = 1)
    (hthree : (1 + 1 + 1 : ZMod p) ≠ 0) :
    (affineCollisionFilter G).card ≤ 4 * B ^ 2 := by
  rw [affineCollisionFilter_card_eq_standard_shift G hclosed hinv h2 hneg htwo0]
  exact card_collision_le_four_sq G hB h2B hB3 hp hpow hthree

namespace F7Audit

open ArkLib.ProximityGap.Frontier.G193SymmetricPatternCovarianceRefuted

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Coefficient absorption is not automatic for genuine multiplicative subgroups: the G193
order-three subgroup contains `2` but not `-1`. -/
theorem two_mem_and_neg_one_not_mem :
    (2 : ZMod 7) ∈ G ∧ (-1 : ZMod 7) ∉ G := by
  decide

#print axioms two_mem_and_neg_one_not_mem

end F7Audit

#print axioms affineCollisionFilter_card_eq_standard_shift
#print axioms affineCollisionFilter_card_le_four_sq

end ArkLib.ProximityGap.Frontier.G200CoefficientAbsorptionStepanov
