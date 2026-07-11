/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G179RepetitionPenaltyTransfer

/-!
# G180: exact dispersion of the depth-two diagonal defect

G179 bounded a nonnegative defect profile only through its total mass, paying the square of that
mass.  At depth two, repeated tuples are diagonal, so their sum profile is the fiber profile of
the doubling map `x ↦ x+x`.  In odd characteristic doubling is injective.  This file proves the
general injective-image identity

`V(t ↦ #{x ∈ G | φ x = t}) = |F| |G| - |G|²`

and specializes it to doubling.  The diagonal defect therefore pays linear, rather than quadratic,
mass in its `L²` term.  This is the base case for a higher-depth collision-partition treatment of
the repetition defect.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G180DiagonalDefectDispersion

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo

variable {F : Type*} [Fintype F] [DecidableEq F]

noncomputable def imageFiberProfile (G : Finset F) (φ : F → F) : F → ℝ :=
  fun t => ((G.filter fun x => φ x = t).card : ℝ)

theorem sum_imageFiberProfile (G : Finset F) (φ : F → F) :
    ∑ t, imageFiberProfile G φ t = G.card := by
  classical
  have hmaps : ∀ x ∈ G, φ x ∈ (Finset.univ : Finset F) := by simp
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  unfold imageFiberProfile
  rw [← Nat.cast_sum]
  exact_mod_cast h.symm

theorem imageFiberProfile_eq_one_of_mem_image {G : Finset F} {φ : F → F}
    (hφ : Set.InjOn φ G) {t : F} (ht : t ∈ G.image φ) :
    imageFiberProfile G φ t = 1 := by
  obtain ⟨x, hxG, hxt⟩ := Finset.mem_image.mp ht
  unfold imageFiberProfile
  norm_cast
  rw [Finset.card_eq_one]
  refine ⟨x, ?_⟩
  ext y
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hyG, hyt⟩
    apply hφ hyG hxG
    exact hyt.trans hxt.symm
  · rintro rfl
    exact ⟨hxG, hxt⟩

theorem imageFiberProfile_eq_zero_of_not_mem_image {G : Finset F} {φ : F → F}
    {t : F} (ht : t ∉ G.image φ) : imageFiberProfile G φ t = 0 := by
  unfold imageFiberProfile
  norm_cast
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hxG hφx
  exact ht (Finset.mem_image.mpr ⟨x, hxG, hφx⟩)

theorem imageFiberProfile_sq {G : Finset F} {φ : F → F} (hφ : Set.InjOn φ G) (t : F) :
    imageFiberProfile G φ t ^ 2 = imageFiberProfile G φ t := by
  by_cases ht : t ∈ G.image φ
  · rw [imageFiberProfile_eq_one_of_mem_image hφ ht]
    norm_num
  · rw [imageFiberProfile_eq_zero_of_not_mem_image ht]
    norm_num

/-- **Injective-image dispersion identity.** A fiber profile of an injection is a set indicator,
so its centered mass is exactly `|F||G|-|G|²`. -/
theorem centeredSqMass_imageFiberProfile (G : Finset F) (φ : F → F)
    (hφ : Set.InjOn φ G) :
    centeredSqMass (imageFiberProfile G φ) =
      (Fintype.card F : ℝ) * G.card - G.card ^ 2 := by
  unfold centeredSqMass
  simp_rw [imageFiberProfile_sq hφ]
  rw [sum_imageFiberProfile]

variable [Field F]

theorem doubling_injective (htwo : (2 : F) ≠ 0) :
    Function.Injective (fun x : F => x + x) := by
  intro x y hxy
  have hmul : (2 : F) * x = 2 * y := by
    simpa [two_mul] using hxy
  exact (mul_left_cancel₀ htwo hmul)

noncomputable def diagonalDefectProfile (G : Finset F) : F → ℝ :=
  imageFiberProfile G fun x => x + x

/-- **Depth-two diagonal dispersion.** In odd characteristic the repeated diagonal has exact
centered mass `|F||G|-|G|²`, versus the generic `|F||G|²` total-mass ceiling. -/
theorem centeredSqMass_diagonalDefectProfile (G : Finset F) (htwo : (2 : F) ≠ 0) :
    centeredSqMass (diagonalDefectProfile G) =
      (Fintype.card F : ℝ) * G.card - G.card ^ 2 := by
  exact centeredSqMass_imageFiberProfile G _ (doubling_injective htwo).injOn

#print axioms sum_imageFiberProfile
#print axioms centeredSqMass_imageFiberProfile
#print axioms doubling_injective
#print axioms centeredSqMass_diagonalDefectProfile

end ArkLib.ProximityGap.Frontier.G180DiagonalDefectDispersion
