import ArkLib.Data.CodingTheory.GuruswamiSudan.DictionaryBridge
import ArkLib.Data.CodingTheory.ProximityGap.HasseMonomial

/-! # Coefficient-vector ↔ bivariate-polynomial dictionary (completion)

Closes the dictionary flagged as "not folded in here" in `ListSizeBound`: the abstract
`GSMultInterp` multiplicity formulation (`hasseCoeff` on `CoeffSpace`) agrees with the
`Polynomial`-side bivariate Hasse–Taylor formulation (`ArkLib.GS.hasseCoeff` on `F[X][Y]`) under
`toPoly`. Hence `GSMultInterp.vanishesToOrder ↔ ArkLib.GS.vanishesToOrder (toPoly c)`, so a GS
interpolant produced by `exists_ne_zero_vanishesToOrder` is a genuine order-`m` vanishing
bivariate polynomial. Proof: linearity (`hasseCoeffLinearMap` + `map_sum`) reduces to the
single-monomial identity `ArkLib.GS.hasseCoeff_monomial`. -/

open Polynomial

namespace GSMultInterp

variable {F : Type} [Field F] [DecidableEq F]

/-- The `Polynomial`-side Hasse coefficient of `toPoly c`, expanded by linearity over the
monomials of `toPoly`. -/
theorem hasseCoeff_toPoly (k D i j : ℕ) (c : CoeffSpace (F := F) k D) (x₀ y₀ : F) :
    ArkLib.GS.hasseCoeff i j (toPoly k D c) x₀ y₀
      = ∑ st : {ab : ℕ × ℕ // ab ∈ monoIdx k D},
          (st.1.1.choose i : F) * (st.1.2.choose j : F) * c st
            * x₀ ^ (st.1.1 - i) * y₀ ^ (st.1.2 - j) := by
  have hlin : ArkLib.GS.hasseCoeff i j (toPoly k D c) x₀ y₀
      = ArkLib.GS.hasseCoeffLinearMap i j x₀ y₀ (toPoly k D c) := rfl
  rw [hlin, toPoly, map_sum]
  refine Finset.sum_congr rfl (fun st _ => ?_)
  rw [ArkLib.GS.hasseCoeffLinearMap_apply, ArkLib.GS.hasseCoeff_monomial]

/-- **Hasse-coefficient agreement.** The abstract `GSMultInterp.hasseCoeff` equals the
`Polynomial`-side bivariate Hasse coefficient of `toPoly c`, for every order `(i,j)` and point. -/
theorem hasseCoeff_eq (k D i j : ℕ) (c : CoeffSpace (F := F) k D) (x₀ y₀ : F) :
    hasseCoeff k D c i j x₀ y₀ = ArkLib.GS.hasseCoeff i j (toPoly k D c) x₀ y₀ := by
  rw [hasseCoeff_toPoly]
  rfl

/-- **The dictionary.** `GSMultInterp`'s order-`m` vanishing of the coefficient vector `c` is
exactly the `Polynomial`-side order-`m` vanishing of `toPoly c` at `(x₀, y₀)`. -/
theorem vanishesToOrder_toPoly_iff (k D m : ℕ) (c : CoeffSpace (F := F) k D) (x₀ y₀ : F) :
    ArkLib.GS.vanishesToOrder m (toPoly k D c) x₀ y₀ ↔ vanishesToOrder k D m c x₀ y₀ := by
  rw [ArkLib.GS.vanishesToOrder_iff_hasseCoeff]
  unfold vanishesToOrder
  refine forall_congr' (fun i => forall_congr' (fun j => ?_))
  rw [hasseCoeff_eq]

end GSMultInterp
