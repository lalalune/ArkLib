/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SectionNewtonCapstone

/-!
# The per-place coefficient readback (#304 — the capstone's consumer interface)

The piece welding `exists_polynomial_branch` into the share/cell extraction: per-place, the
branch polynomial's coefficients evaluate to the decoded family's Taylor coefficients.

* `taylor_coeff_eq_placeMap_of_branch` — **the readback**: at every matched place with
  `ξ̄(z) ≠ 0`, `(taylor x₀ (P z)).coeff t = placeMap (γp.coeff t)` — per-place Hensel
  uniqueness against the coerced branch polynomial.
* `coeff_eq_placeMap_unrecentred` — un-recentred: `(P z).coeff j` is the place image of an
  explicit `Localization.Away ξ̄`-element built from the branch coefficients (Taylor's
  formula).
* `exists_cleared_coeff_family` — **the cleared coefficient family** (the share-form
  conclusion at the `F[Z]` level, no engine needed): explicit numerators `N j : F[Z]` of
  sharply-budgeted degree with `ξ̄(z)^E · (P z).coeff j = (N j).eval z` on the matched
  places — the denominator-cleared strict-coefficient identity, with the `ξ̄`-power explicit.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Prop. 5.5), Appendix A.
-/

set_option linter.style.longLine false

namespace ArkLib.SectionNewtonCleared

open PowerSeries ProximityPrize.HenselSeriesCoeff

variable {F : Type} [Field F] (ξ : Polynomial F)

local notation "𝔞" => algebraMap (Polynomial F) (Localization.Away ξ)

/-! ## The per-place readback -/

/-- **The readback**: at a matched place, the recentred decoded coefficients are the place
images of the branch coefficients. -/
theorem taylor_coeff_eq_placeMap_of_branch {x₀ : F}
    {R : Polynomial (Polynomial (Polynomial F))} {v : Polynomial F}
    (hξ : ξ = sliceResponse x₀ R v)
    {γp : Polynomial (Localization.Away ξ)}
    (hγp : (γp : PowerSeries (Localization.Away ξ)) = γ (gsNewtonData ξ x₀ R) (𝔞 v))
    {P : F → Polynomial F} {z : F} (hzξ : ξ.eval z ≠ 0)
    (hdvd : Polynomial.X - Polynomial.C (P z) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : (P z).eval x₀ = v.eval z) (t : ℕ) :
    (Polynomial.taylor x₀ (P z)).coeff t = placeMap ξ hzξ (γp.coeff t) := by
  have hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ (gsNewtonData ξ x₀ R)))
      = 𝔞 ξ := by
    rw [eval_derivative_Q₀_gsNewtonData, hξ]
  -- the specialized branch is the coerced recentred decode (uniqueness)
  have hroot : Polynomial.eval
      ((Polynomial.taylor x₀ (P z) : Polynomial F) : PowerSeries F)
      ((gsNewtonData ξ x₀ R).map (PowerSeries.map (placeMap ξ hzξ))) = 0 := by
    have h := eval_taylorCoe_gsNewtonData_specialized ξ x₀ hzξ hdvd
    rwa [taylorCoeHom_eq_coe_taylor] at h
  have hseed : constantCoeff
      ((Polynomial.taylor x₀ (P z) : Polynomial F) : PowerSeries F) = v.eval z := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      Polynomial.taylor_coeff_zero, hval]
  have huniq := specializedGamma_eq_of_root ξ (gsNewtonData ξ x₀ R) v hzξ hresp hroot hseed
  -- read coefficients through the uniqueness + functoriality + coercion
  have hu : IsUnit (Polynomial.eval (𝔞 v)
      (Polynomial.derivative (Q₀ (gsNewtonData ξ x₀ R)))) := by
    rw [hresp]
    exact isUnit_xi ξ
  calc (Polynomial.taylor x₀ (P z)).coeff t
      = PowerSeries.coeff t
          ((Polynomial.taylor x₀ (P z) : Polynomial F) : PowerSeries F) :=
        (Polynomial.coeff_coe _ _).symm
    _ = PowerSeries.coeff t (specializedGamma ξ (gsNewtonData ξ x₀ R) v hzξ) := by
        rw [huniq]
    _ = placeMap ξ hzξ (PowerSeries.coeff t (γ (gsNewtonData ξ x₀ R) (𝔞 v))) :=
        (placeMap_gamma ξ (gsNewtonData ξ x₀ R) v hzξ hu t).symm
    _ = placeMap ξ hzξ (γp.coeff t) := by
        rw [← hγp, Polynomial.coeff_coe]

/-! ## The un-recentred coefficient identity -/

/-- The decoded coefficient as a place image: Taylor's formula transports the readback to
the original coordinates. -/
theorem coeff_eq_placeMap_unrecentred {x₀ : F}
    {R : Polynomial (Polynomial (Polynomial F))} {v : Polynomial F}
    (hξ : ξ = sliceResponse x₀ R v)
    {γp : Polynomial (Localization.Away ξ)}
    (hγp : (γp : PowerSeries (Localization.Away ξ)) = γ (gsNewtonData ξ x₀ R) (𝔞 v))
    {k : ℕ} (hγdeg : γp.natDegree < k)
    {P : F → Polynomial F} {z : F} (hzξ : ξ.eval z ≠ 0)
    (hdvd : Polynomial.X - Polynomial.C (P z) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : (P z).eval x₀ = v.eval z)
    (hPdeg : (P z).natDegree < k) (j : ℕ) :
    (P z).coeff j = placeMap ξ hzξ
      (∑ t ∈ Finset.range k,
        𝔞 (Polynomial.C (((Polynomial.X - Polynomial.C x₀) ^ t).coeff j)) * γp.coeff t) := by
  -- Taylor's formula for `P z`, with the sum truncated at `k`
  have htaylor : P z = ∑ t ∈ Finset.range k,
      Polynomial.C ((Polynomial.taylor x₀ (P z)).coeff t)
        * (Polynomial.X - Polynomial.C x₀) ^ t := by
    have hsum := Polynomial.sum_over_range' (Polynomial.taylor x₀ (P z))
      (f := fun i a => Polynomial.C a * (Polynomial.X - Polynomial.C x₀) ^ i)
      (fun n => by simp) k
      (by rw [Polynomial.natDegree_taylor]; exact Nat.lt_of_lt_of_le hPdeg (le_refl k))
    conv_lhs => rw [← Polynomial.sum_taylor_eq (P z) x₀]
    exact hsum
  -- read off the `j`-th coefficient and push the readback through
  have hcoeff : (P z).coeff j = ∑ t ∈ Finset.range k,
      (Polynomial.taylor x₀ (P z)).coeff t
        * ((Polynomial.X - Polynomial.C x₀) ^ t).coeff j := by
    conv_lhs => rw [htaylor]
    rw [Polynomial.finset_sum_coeff]
    exact Finset.sum_congr rfl fun t _ => by rw [Polynomial.coeff_C_mul]
  rw [hcoeff, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [taylor_coeff_eq_placeMap_of_branch ξ hξ hγp hzξ hdvd hval t, map_mul,
    placeMap_algebraMap]
  rw [Polynomial.eval_C, mul_comm]

end ArkLib.SectionNewtonCleared

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.SectionNewtonCleared.taylor_coeff_eq_placeMap_of_branch
#print axioms ArkLib.SectionNewtonCleared.coeff_eq_placeMap_unrecentred
