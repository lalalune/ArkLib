/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

set_option linter.style.longLine false

/-!
# The dilation / Hadamard recursion for subgroup Gauss sums, and exact L²-doubling (#407)

The prize-deciding object is `B = max_{b≠0} ‖η_b‖`, `η_b = ∑_{x∈G} ψ(b·x)` for the smooth
`2^μ`-subgroup `G = μ_n`. The 2-power tower `μ_{2^{i+1}} = μ_{2^i} ⊔ ζ·μ_{2^i}` (`ζ` a primitive
`2^{i+1}`-th root) makes the incomplete sums a **non-autonomous Hadamard recursion in the dilate**:
each level-`(i+1)` frequency value is its own level-`i` value plus the value of its **dilate** `ζ·b`.

This file proves the two exact, fully elementary facts of that recursion (no Weil, no Stepanov),
stated generally for **any** finite set `G` and any nonzero "dilation" scalar `ζ`:

* `eta_dilate`        : `η_b(ζ•G) = η_{ζ·b}(G)`            (reindex the image set).
* `eta_union_dilate`  : if `G` and `ζ•G` are **disjoint**, `η_b(G ⊔ ζ•G) = η_b(G) + η_{ζ·b}(G)`
                        — **THE RECURSION** (`f_{i+1}(b) = f_i(b) + f_i(ζb)`).
* `eta_dilate_secondMoment_doubling` :
    `∑_b ‖η_b(G ⊔ ζ•G)‖² = 2·∑_b ‖η_b(G)‖²`  — **exact L²-doubling**.

The doubling is the *easy / Johnson-side* direction: it is a clean corollary of the second-moment
identity `∑_b ‖η_b‖² = q·|G|` (`subgroup_gaussSum_secondMoment`, pure additive-character
orthogonality), since a disjoint dilate union just doubles `|G|`. Equivalently, the L²
cross-correlation `∑_b η_b(G)·conj η_{ζb}(G) = q·|G ∩ ζ•G|` **vanishes** on a disjoint union —
this is exactly the orthogonality already baked into the second moment.

Honest scope: this is the L² (energy) layer, which is **domain-blind and Johnson-capped**. The
prize floor needs the L^∞ (sup over `b`) bound, where the recursion only gives the trivial
`max_{b}‖η_b(G ⊔ ζ•G)‖ ≤ 2·max_b‖η_b(G)‖` (children can phase-align); beating it is the
cocycle large-deviation = the open BGK short-character-sum bound. See
`docs/kb/deltastar-dilation-recursion-reformulation-2026-06-13.md` and
`scripts/probes/probe_dilation_recursion_tower.py`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
-/

open Finset AddChar

namespace ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The **dilated set** `ζ•G = {ζ·x : x ∈ G}`. -/
noncomputable def dilate (ζ : F) (G : Finset F) : Finset F := G.image (fun x => ζ * x)

/-- For `ζ ≠ 0`, multiplication by `ζ` is injective on `F`. -/
private lemma mul_left_inj_of_ne_zero {ζ : F} (hζ : ζ ≠ 0) :
    Function.Injective (fun x : F => ζ * x) :=
  fun _ _ h => mul_left_cancel₀ hζ h

/-- **The dilation reindex: `η_b(ζ•G) = η_{ζ·b}(G)`.** -/
theorem eta_dilate (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0) (b : F) :
    eta ψ (dilate ζ G) b = eta ψ G (ζ * b) := by
  unfold eta dilate
  rw [Finset.sum_image (fun x _ y _ h => mul_left_inj_of_ne_zero hζ h)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  ring

/-- **|ζ•G| = |G|** for `ζ ≠ 0` (image under an injection). -/
theorem card_dilate {ζ : F} (hζ : ζ ≠ 0) (G : Finset F) : (dilate ζ G).card = G.card :=
  Finset.card_image_of_injective G (mul_left_inj_of_ne_zero hζ)

/-- **THE DILATION RECURSION** `f_{i+1}(b) = f_i(b) + f_i(ζ·b)`. -/
theorem eta_union_dilate (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint G (dilate ζ G)) (b : F) :
    eta ψ (G ∪ dilate ζ G) b = eta ψ G b + eta ψ G (ζ * b) := by
  rw [← eta_dilate ψ G hζ b]
  unfold eta
  rw [Finset.sum_union hdisj]

/-- **EXACT L²-DOUBLING** `∑_b ‖η_b(G ⊔ ζ•G)‖² = 2·∑_b ‖η_b(G)‖²`. -/
theorem eta_dilate_secondMoment_doubling {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {ζ : F} (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) :
    ∑ b : F, ‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 = 2 * ∑ b : F, ‖eta ψ G b‖ ^ 2 := by
  rw [subgroup_gaussSum_secondMoment hψ (G ∪ dilate ζ G),
      subgroup_gaussSum_secondMoment hψ G,
      Finset.card_union_of_disjoint hdisj, card_dilate hζ G]
  push_cast
  ring

end ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
