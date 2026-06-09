/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BetaWeightGradedAssembly
import ArkLib.ToMathlib.BetaInputSupply

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

variable {F : Type} [Field F]

/-- Right-multiplication monotonicity for `WithBot ℕ` weight bounds (local copy of the
private `BetaInputSupply` helper). -/
private theorem withBot_mul_right_le' {a : WithBot ℕ} {c d : ℕ}
    (h : a ≤ (c : WithBot ℕ)) : a * (d : WithBot ℕ) ≤ ((c * d : ℕ) : WithBot ℕ) := by
  have hcd : ((c * d : ℕ) : WithBot ℕ) = (c : WithBot ℕ) * (d : WithBot ℕ) := by
    push_cast; ring
  rw [hcd]
  gcongr

/-- **The graded finite-range `hcardFin` bridge (canonical `Bcoeff`).** A concrete cardinality
bound at the graded budget `(α(2t−1)+A)·d_H` on `[k,T]` yields the exact
`Section5StrictDataFin.hcardFin` field, via `betaRec_weight_le_graded`. -/
theorem hcardFin_of_graded (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    {D k T : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {matchingSet : Finset F}
    (hconcreteFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > ((((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1))
                * (2 * t - 1)
              + (D - H.natDegree + 1)) * H.natDegree : ℕ) : WithBot ℕ)) :
    ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
      > weight_Λ_over_𝒪 hH
          (betaRec x₀ R H hHyp (BCIKS20.HenselNumerator.B_coeff H x₀ R) t) D
        * H.natDegree := by
  intro t hkt htT
  have hwt := betaRec_weight_le_graded x₀ R H hHyp hD hH hmonic hd2 hdHD hD_Rx0 hR t
  have hmul : weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp (BCIKS20.HenselNumerator.B_coeff H x₀ R) t) D
        * (H.natDegree : WithBot ℕ)
      ≤ ((((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1))
              * (2 * t - 1)
            + (D - H.natDegree + 1)) * H.natDegree : ℕ) : WithBot ℕ) :=
    withBot_mul_right_le' (by simpa using hwt)
  exact lt_of_le_of_lt hmul (hconcreteFin t hkt htT)

end ArkLib

#print axioms ArkLib.hcardFin_of_graded
