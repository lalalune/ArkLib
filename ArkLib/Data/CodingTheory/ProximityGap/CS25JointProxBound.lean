/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentReduction

/-!
# Counting jointly-close stacks (toward T4.17, #82)

Toward the `#{jointProx}` upper bound needed to assemble the CS25 complete-CA-breakdown count
budget `hfar`. This file first establishes the cardinality of the interleaved code: a stack is
jointly `δ`-close to `C` iff its interleaving `⋈|u = uᵀ` is close to *some* interleaved codeword,
and the interleaved code `C^⋈κ = {V | ∀ k, V.transpose k ∈ C}` has exactly `|C|^|κ|` codewords
(it is the `κ`-fold product of `C`, via the transpose bijection).
-/

open Code
open scoped NNReal

namespace CS25

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- **The interleaved code is the `κ`-fold product of `C`.** As a type, `C^⋈κ ≃ (κ → C)` via the
transpose map `V ↦ (k ↦ Vᵀ k)`. -/
def interleavedCodeSetEquiv (C : Set (ι → A)) :
    ↥(interleavedCodeSet (κ := κ) C) ≃ (κ → ↥C) where
  toFun := fun V k => ⟨V.1.transpose k, V.2 k⟩
  invFun := fun g => ⟨Matrix.of (fun i k => (g k).1 i), fun k => (g k).2⟩
  left_inv := fun V => by ext i k; rfl
  right_inv := fun g => by ext k i; rfl

/-- **The interleaved code `C^⋈κ` has `|C|^|κ|` codewords.** -/
theorem interleavedCodeSet_card (C : Set (ι → A)) [Fintype ↥C]
    [Fintype ↥(interleavedCodeSet (κ := κ) C)] :
    Fintype.card ↥(interleavedCodeSet (κ := κ) C) = (Fintype.card ↥C) ^ (Fintype.card κ) := by
  rw [Fintype.card_congr (interleavedCodeSetEquiv (κ := κ) C), Fintype.card_fun]

/-- **Union (covering) upper bound.** For any finite code `𝒞`, the number of words within Hamming
distance `r` of `𝒞` is at most `|𝒞| · V` (the union bound). Derived from the first moment
`ArkLib.CS25.sum_closeCount_eq`: each covered word has `closeCount ≥ 1`. -/
theorem card_close_le_card_mul_vol {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]
    (𝒞 : Finset (ι → F)) (r : ℕ) :
    (Finset.univ.filter (fun w : ι → F => ArkLib.CS25.closeCount 𝒞 r w ≠ 0)).card
      ≤ 𝒞.card * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card := by
  classical
  calc (Finset.univ.filter (fun w : ι → F => ArkLib.CS25.closeCount 𝒞 r w ≠ 0)).card
      = ∑ w : ι → F, (if ArkLib.CS25.closeCount 𝒞 r w ≠ 0 then 1 else 0) := by
        rw [Finset.card_filter]
    _ ≤ ∑ w : ι → F, ArkLib.CS25.closeCount 𝒞 r w := by
        refine Finset.sum_le_sum (fun w _ => ?_)
        by_cases h : ArkLib.CS25.closeCount 𝒞 r w ≠ 0
        · rw [if_pos h]; omega
        · rw [if_neg h]; exact Nat.zero_le _
    _ = 𝒞.card * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card :=
        ArkLib.CS25.sum_closeCount_eq 𝒞 r

open Classical in
/-- **Jointly-`e`-close stack count bound.** A stack `u` is jointly `e`-close to `C` iff its
interleaving `⋈|u = uᵀ` is within Hamming distance `e` of some interleaved codeword. By the union
bound over the interleaved code `C^⋈κ` (`|C|^|κ|` codewords), the number of jointly-`e`-close stacks
is at most `|C|^|κ| · V'`, where `V'` is the interleaved-ball volume. -/
theorem card_jointProximityNat_le (C : Set (ι → A)) [AddCommGroup A] [Fintype ↥C] (e : ℕ) :
    (Finset.univ.filter (fun u : WordStack A κ ι => jointProximityNat C (u := u) e)).card
      ≤ (Fintype.card ↥C) ^ (Fintype.card κ)
        * (Finset.univ.filter (fun w : InterleavedWord A κ ι => hammingDist w 0 ≤ e)).card := by
  classical
  -- the interleaved code, as the image Finset of its codeword subtype (avoids `Set.toFinset`)
  set 𝒞 : Finset (InterleavedWord A κ ι) :=
    Finset.univ.image (fun v : ↥(interleavedCodeSet (κ := κ) C) => v.val) with h𝒞
  have hiff : ∀ u : WordStack A κ ι,
      jointProximityNat C (u := u) e ↔ ArkLib.CS25.closeCount 𝒞 e u.transpose ≠ 0 := by
    intro u
    rw [jointProximityNat_iff_closeToInterleavedCodeword, ArkLib.CS25.closeCount,
      Finset.card_ne_zero, Finset.filter_nonempty_iff]
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨v.val, Finset.mem_image_of_mem _ (Finset.mem_univ v), hv⟩
    · rintro ⟨c, hcS, hc⟩
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hcS
      exact ⟨v, hc⟩
  have hreindex :
      (Finset.univ.filter (fun u : WordStack A κ ι => jointProximityNat C (u := u) e)).card
        = (Finset.univ.filter (fun w : InterleavedWord A κ ι =>
            ArkLib.CS25.closeCount 𝒞 e w ≠ 0)).card := by
    refine Finset.card_nbij' (fun u => u.transpose) (fun w => w.transpose) ?_ ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact (hiff u).mp hu
    · intro w hw
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rw [hiff]; simpa [Matrix.transpose_transpose] using hw
    · intro u _; simp [Matrix.transpose_transpose]
    · intro w _; simp [Matrix.transpose_transpose]
  rw [hreindex]
  calc (Finset.univ.filter (fun w : InterleavedWord A κ ι =>
            ArkLib.CS25.closeCount 𝒞 e w ≠ 0)).card
      ≤ 𝒞.card
          * (Finset.univ.filter (fun w : InterleavedWord A κ ι => hammingDist w 0 ≤ e)).card :=
        card_close_le_card_mul_vol _ e
    _ = (Fintype.card ↥C) ^ (Fintype.card κ)
          * (Finset.univ.filter (fun w : InterleavedWord A κ ι => hammingDist w 0 ≤ e)).card := by
        rw [h𝒞, Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ,
          interleavedCodeSet_card]

/-- **Bridge.** Relative joint proximity at `δ` is absolute joint proximity at `⌊δ·n⌋`. Immediate
from `Code.relDistFromCode_le_iff_distFromCode_le` (`δᵣ ≤ δ ↔ Δ₀ ≤ ⌊δ·n⌋`). -/
theorem jointProximity_iff_jointProximityNat [Nonempty ι] (C : Set (ι → A))
    (u : WordStack A κ ι) (δ : ℝ≥0) :
    jointProximity C (u := u) δ ↔
      jointProximityNat C (u := u) ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := by
  unfold jointProximity jointProximityNat
  exact Code.relDistFromCode_le_iff_distFromCode_le _ δ

open Classical in
/-- **Jointly-`δ`-close stack count bound (relative form).** The number of stacks jointly within
relative distance `δ` of `C` is at most `|C|^|κ| · V'`, where `V'` is the interleaved-ball volume at
radius `⌊δ·n⌋`. This is ingredient (b) of the CS25 complete-CA-breakdown count budget `hfar`. -/
theorem card_jointProximity_le [Nonempty ι] (C : Set (ι → A)) [AddCommGroup A] [Fintype ↥C]
    (δ : ℝ≥0) :
    (Finset.univ.filter (fun u : WordStack A κ ι => jointProximity C (u := u) δ)).card
      ≤ (Fintype.card ↥C) ^ (Fintype.card κ)
        * (Finset.univ.filter (fun w : InterleavedWord A κ ι =>
            hammingDist w 0 ≤ ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊)).card := by
  have hset :
      (Finset.univ.filter (fun u : WordStack A κ ι => jointProximity C (u := u) δ))
        = (Finset.univ.filter (fun u : WordStack A κ ι =>
            jointProximityNat C (u := u) ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact jointProximity_iff_jointProximityNat C u δ
  rw [hset]
  exact card_jointProximityNat_le C _

end CS25
