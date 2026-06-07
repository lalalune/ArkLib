import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

theorem liftToFunctionField_injective : Function.Injective (liftToFunctionField (H := H)) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hne
  exact liftToFunctionField_ne_zero hne hp

theorem coeToPowerSeries_ringHom_injective :
    Function.Injective (Polynomial.coeToPowerSeries.ringHom (R := 𝕃 H)) := by
  intro a b hab
  apply Polynomial.coe_injective (𝕃 H)
  simpa [Polynomial.coeToPowerSeries.ringHom] using hab

theorem taylorAlgHom_toRingHom_injective (x₀ : F) :
    Function.Injective ⇑(Polynomial.taylorAlgHom (R := F[X]) (Polynomial.C x₀)).toRingHom := by
  intro a b hab
  apply Polynomial.taylor_injective (Polynomial.C x₀)
  have h : ∀ q : F[X][Y], (Polynomial.taylorAlgHom (R := F[X]) (Polynomial.C x₀)).toRingHom q
      = Polynomial.taylor (Polynomial.C x₀) q := fun q => by simp [Polynomial.taylorAlgHom_apply]
  rw [h, h] at hab; exact hab

theorem mapRingHom_lift_injective :
    Function.Injective ⇑(Polynomial.mapRingHom (liftToFunctionField (H := H))) := by
  rw [Polynomial.coe_mapRingHom]
  exact Polynomial.map_injective _ (liftToFunctionField_injective H)

theorem coeffHom_injective (x₀ : F) : Function.Injective (coeffHom x₀ H) := by
  have h1 := coeToPowerSeries_ringHom_injective H
  have h2 := mapRingHom_lift_injective H
  have h3 := taylorAlgHom_toRingHom_injective (F := F) x₀
  rw [coeffHom]
  -- coeffHom = coeToPowerSeries.ringHom ∘ (mapRingHom ∘ taylorAlgHom.toRingHom)
  rw [RingHom.coe_comp, RingHom.coe_comp]
  exact h1.comp (h2.comp h3)

theorem Q_natDegree_eq (x₀ : F) (R : F[X][X][Y]) :
    (Q x₀ R H).natDegree = R.natDegree := by
  rw [Q, Polynomial.natDegree_map_eq_of_injective (coeffHom_injective H x₀)]

end BCIKS20.HenselNumerator
