/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator

/-!
# The Hasse `Δ_Y` index-shift degree drop (Johnson E1′, transcription item (a))

DISPROOF_LOG O154 finding 7: the per-term weight bound of the Claim A.2 structured
induction needs, for the `B`-coefficient estimate, the **index-shift** property of the
`Y`-Hasse derivative — the `j`-th coefficient of `Δ_Y^{m} R` is `C(j+m, m) • R.coeff (j+m)`
(Mathlib's `hasseDeriv_coeff`), so its inner degree is bounded by that of the *shifted*
coefficient. In the total-degree shape (`deg coeff_i ≤ D_R − i`) this yields the drop
`deg ((Δ_Y^m R).coeff j) ≤ (D_R − m) − j` — the `−m` that finding 7's arithmetic consumes.

* `hasseDerivY_coeff` — the coefficient identity, specialized to the in-tree `hasseDerivY`;
* `hasseDerivY_coeff_natDegree_le` — the per-coefficient degree bound (shift form);
* `hasseDerivY_coeff_natDegree_le_of_total` — the total-degree-shape drop.

All char-free (the binomial scalar may vanish in positive characteristic; degree bounds
survive since `natDegree (n • p) ≤ natDegree p` unconditionally).
-/

open Polynomial Polynomial.Bivariate

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]

/-- The coefficient identity for the in-tree `Δ_Y`: the `j`-th coefficient of
`Δ_Y^{m} R` is the binomial multiple of the `(j+m)`-th coefficient of `R`. -/
theorem hasseDerivY_coeff (m j : ℕ) (R : F[X][X][Y]) :
    (hasseDerivY m R).coeff j = ((j + m).choose m : F[X][X]) * R.coeff (j + m) := by
  unfold hasseDerivY
  exact Polynomial.hasseDeriv_coeff (k := m) (f := R) j

/-- **The index-shift degree bound:** the `j`-th coefficient of `Δ_Y^{m} R` has inner
degree at most that of `R.coeff (j + m)`. -/
theorem hasseDerivY_coeff_natDegree_le (m j : ℕ) (R : F[X][X][Y]) :
    ((hasseDerivY m R).coeff j).natDegree ≤ (R.coeff (j + m)).natDegree := by
  rw [hasseDerivY_coeff]
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  simp [Polynomial.natDegree_natCast]

/-- **The total-degree-shape drop** (the form finding 7 consumes): if `R`'s coefficients
satisfy the total-degree bound `deg (R.coeff i) ≤ D_R − i`, then the `m`-th `Y`-Hasse
derivative satisfies `deg ((Δ_Y^m R).coeff j) ≤ (D_R − m) − j`: the whole budget drops
by `m`. -/
theorem hasseDerivY_coeff_natDegree_le_of_total {R : F[X][X][Y]} {DR : ℕ}
    (htotal : ∀ i, (R.coeff i).natDegree ≤ DR - i) (m j : ℕ) :
    ((hasseDerivY m R).coeff j).natDegree ≤ (DR - m) - j := by
  calc ((hasseDerivY m R).coeff j).natDegree
      ≤ (R.coeff (j + m)).natDegree := hasseDerivY_coeff_natDegree_le m j R
    _ ≤ DR - (j + m) := htotal (j + m)
    _ = (DR - m) - j := by omega

/-! ## Source audit -/

#print axioms hasseDerivY_coeff
#print axioms hasseDerivY_coeff_natDegree_le
#print axioms hasseDerivY_coeff_natDegree_le_of_total

end BCIKS20.HenselNumerator
