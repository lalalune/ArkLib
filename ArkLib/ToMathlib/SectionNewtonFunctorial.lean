/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.HenselSeriesCoeff

/-!
# Functoriality of the Newton iteration (#304, the section-Newton transport unifier)

The series-coefficient Newton iteration of `HenselSeriesCoeff` (`S`, `γ`) commutes with any
ring homomorphism `φ : R →+* R'` mapping the data, **provided the source derivative response
is a unit**: `PowerSeries.map φ (γ Q c) = γ (Q.map (PowerSeries.map φ)) (φ c)`
(`map_γ`, coefficient form `coeff_map_γ`).

This is THE transport unifier of the elementary section-Newton route: instantiated at the
localization `A := Localization.Away ξ̄` of `F[Z]` (where the derivative response ξ̄ **is** a
unit), the two maps

* `A →+* RatFunc F` (the global fraction embedding), and
* `A →+* F` (per-place evaluation at `z` with `ξ̄(z) ≠ 0`, via `Localization.awayLift`)

carry the SAME Newton iterate `γ_A` to the global `γ_K` (the object the engine and the
tail/window machinery consume) and to the per-place specialized iterate (the object per-place
Hensel uniqueness pins to the decoded Taylor series).  One lemma replaces both transport
chains of the legacy `𝒪/𝕃`-route (`LocalizationEmbedding` + `LocalizedPlaceEvaluation` +
`AssembledRootDescent`).

The unit hypothesis is genuinely needed on the source: the recursion divides by
`Ring.inverse` of the response, and `Ring.inverse` commutes with `φ` **only at units**
(`φ` can create units — e.g. `eval z : F[Z] → F` makes `ξ̄` invertible at `ξ̄(z) ≠ 0` —
and on a non-unit source `Ring.inverse = 0` while the target inverse is genuine).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5, Appendix A (the per-place projections `π_z`).
-/

set_option linter.style.longLine false

namespace ProximityPrize.HenselSeriesCoeff

open PowerSeries

variable {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
variable (Q : Polynomial R⟦X⟧) (c : R)

/-- `Ring.inverse` commutes with ring homomorphisms **at units**. -/
theorem ringInverse_map {u : R} (hu : IsUnit u) :
    φ (Ring.inverse u) = Ring.inverse (φ u) := by
  have h1 : φ (Ring.inverse u) * φ u = 1 := by
    rw [← map_mul, Ring.inverse_mul_cancel _ hu, map_one]
  have h2 : Ring.inverse (φ u) * φ u = 1 :=
    Ring.inverse_mul_cancel _ (hu.map φ)
  calc φ (Ring.inverse u) = φ (Ring.inverse u) * (Ring.inverse (φ u) * φ u) := by
        rw [h2, mul_one]
    _ = (φ (Ring.inverse u) * φ u) * Ring.inverse (φ u) := by ring
    _ = Ring.inverse (φ u) := by rw [h1, one_mul]

/-- The order-`0` reduction commutes with coefficient maps. -/
theorem Q₀_map :
    Q₀ (Q.map (PowerSeries.map φ : R⟦X⟧ →+* R'⟦X⟧)) = (Q₀ Q).map φ := by
  unfold Q₀
  rw [Polynomial.map_map, Polynomial.map_map]
  congr 1
  ext f : 1
  exact PowerSeries.constantCoeff_map φ f

/-- The derivative response commutes: the target response is the `φ`-image of the source's. -/
theorem eval_derivative_Q₀_map :
    Polynomial.eval (φ c) (Polynomial.derivative
        (Q₀ (Q.map (PowerSeries.map φ : R⟦X⟧ →+* R'⟦X⟧))))
      = φ (Polynomial.eval c (Polynomial.derivative (Q₀ Q))) := by
  rw [Q₀_map, ← Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_hom]

/-- Polynomial evaluation over power series commutes with coefficient maps. -/
theorem map_eval_powerSeries (γ : R⟦X⟧) :
    (PowerSeries.map φ) (Polynomial.eval γ Q)
      = Polynomial.eval ((PowerSeries.map φ) γ)
          (Q.map (PowerSeries.map φ : R⟦X⟧ →+* R'⟦X⟧)) := by
  rw [Polynomial.eval_map, ← Polynomial.eval₂_id_eq_eval]
  · exact (Polynomial.hom_eval₂ Q (RingHom.id _) (PowerSeries.map φ) γ).trans
      (by rw [RingHom.comp_id])

variable (hu : IsUnit (Polynomial.eval c (Polynomial.derivative (Q₀ Q))))

include hu in
/-- **Functoriality of the Newton iteration**: partial sums commute with any coefficient map
that sees a unit source response. -/
theorem map_S (t : ℕ) :
    (PowerSeries.map φ) (S Q c t)
      = S (Q.map (PowerSeries.map φ : R⟦X⟧ →+* R'⟦X⟧)) (φ c) t := by
  induction t with
  | zero => rw [S, S, PowerSeries.map_C]
  | succ t ih =>
      rw [S, S, map_add, PowerSeries.map_monomial, ih]
      congr 2
      rw [map_mul, map_neg, ringInverse_map φ hu, eval_derivative_Q₀_map,
        ← PowerSeries.coeff_map, map_eval_powerSeries, ih]

include hu in
/-- **Functoriality of the Newton root**: `γ` commutes with any coefficient map that sees a
unit source response.  Instantiations: the global fraction embedding and every per-place
evaluation with nonvanishing response. -/
theorem map_γ :
    (PowerSeries.map φ) (γ Q c)
      = γ (Q.map (PowerSeries.map φ : R⟦X⟧ →+* R'⟦X⟧)) (φ c) := by
  ext t
  rw [PowerSeries.coeff_map, coeff_γ, coeff_γ, ← map_S φ Q c hu t, PowerSeries.coeff_map]

include hu in
/-- Coefficient form of the functoriality. -/
theorem coeff_map_γ (t : ℕ) :
    φ (coeff t (γ Q c))
      = coeff t (γ (Q.map (PowerSeries.map φ : R⟦X⟧ →+* R'⟦X⟧)) (φ c)) := by
  rw [← PowerSeries.coeff_map, map_γ φ Q c hu]

include hu in
/-- **Vanishing transport**: a coefficient window-vanish over the source transports to any
target along the coefficient map.  (For the section-Newton route: prove the window vanish
once over `Localization.Away ξ̄`, export it to `RatFunc F`.) -/
theorem coeff_map_γ_eq_zero {t : ℕ} (h : coeff t (γ Q c) = 0) :
    coeff t (γ (Q.map (PowerSeries.map φ : R⟦X⟧ →+* R'⟦X⟧)) (φ c)) = 0 := by
  rw [← coeff_map_γ φ Q c hu, h, map_zero]

include hu in
/-- **Vanishing reflection along injective maps**: target window-vanish reflects to the
source.  (For the section-Newton route: per-place counting kills the localized coefficient;
injectivity of `Localization.Away ξ̄ →+* RatFunc F` is standard.) -/
theorem coeff_γ_eq_zero_of_map (hinj : Function.Injective φ) {t : ℕ}
    (h : coeff t (γ (Q.map (PowerSeries.map φ : R⟦X⟧ →+* R'⟦X⟧)) (φ c)) = 0) :
    coeff t (γ Q c) = 0 := by
  apply hinj
  rw [coeff_map_γ φ Q c hu, h, map_zero]

end ProximityPrize.HenselSeriesCoeff

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ProximityPrize.HenselSeriesCoeff.ringInverse_map
#print axioms ProximityPrize.HenselSeriesCoeff.Q₀_map
#print axioms ProximityPrize.HenselSeriesCoeff.eval_derivative_Q₀_map
#print axioms ProximityPrize.HenselSeriesCoeff.map_eval_powerSeries
#print axioms ProximityPrize.HenselSeriesCoeff.map_S
#print axioms ProximityPrize.HenselSeriesCoeff.map_γ
#print axioms ProximityPrize.HenselSeriesCoeff.coeff_map_γ
#print axioms ProximityPrize.HenselSeriesCoeff.coeff_map_γ_eq_zero
#print axioms ProximityPrize.HenselSeriesCoeff.coeff_γ_eq_zero_of_map
