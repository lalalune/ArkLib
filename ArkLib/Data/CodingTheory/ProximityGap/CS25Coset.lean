/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallIntersection

/-!
# CS25 #82, deliverable 2 (b/d): the coset identity

The Fourier/MacWilliams route to the second-moment tail.  The total ball-intersection over the code

  `T = ∑_{c∈RS} I(c) = ∑_{c∈RS} |B(0,δ) ∩ B(c,δ)|`

equals the number of **pairs in the ball whose difference lies in the code**:

  `T = #{(w,f) ∈ B(0,δ)² : w - f ∈ RS}`,

via the reindexing `(c, w) ↦ (w, w - c)` together with `δᵣ(w, c) = δᵣ(w - c, 0)`.  This is the
entry point to `T = ∑_κ |B(0,δ) ∩ κ|²` (cosets) and the Fourier bound
`∑_{y∈RS^⊥} |Ŝ(y)|²`, the elegant replacement for the ball-intersection multinomial.
-/

open scoped BigOperators ENNReal NNReal

namespace ArkLib.CS25

open Code Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- `δᵣ(w, w - f) = δᵣ(f, 0)`: the relative distance from `w` to `w - f` is the relative weight
of `f`. -/
theorem relHammingDist_self_sub (w f : ι → F) :
    relHammingDist w (w - f) = relHammingDist f (0 : ι → F) := by
  rw [relHammingDist_eq_sub w (w - f)]
  congr 1
  abel

/-- **Coset identity.** For a finite code `C`, the total ball-intersection `∑_{c∈C} I(c)` equals the
number of pairs of ball points whose difference lies in `C`. -/
theorem sum_jointCoverCount_eq_pairs (C : Finset (ι → F)) (δ : ℝ≥0) :
    (∑ c ∈ C, jointCoverCount δ (0 : ι → F) c)
      = (((C.product (Finset.univ : Finset (ι → F)))).filter
          (fun cw : (ι → F) × (ι → F) =>
            (relHammingDist cw.2 (0 : ι → F) : ENNReal) ≤ (δ : ENNReal)
              ∧ (relHammingDist cw.2 cw.1 : ENNReal) ≤ (δ : ENNReal))).card := by
  classical
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [jointCoverCount, Finset.card_filter]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rfl

end ArkLib.CS25
