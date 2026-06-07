import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ### Injectivity of the coefficient ring hom `coeffHom`, hence `Q.natDegree = R.natDegree`. -/

private theorem liftToFunctionField_injective_tc :
    Function.Injective (liftToFunctionField (H := H)) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hne
  exact liftToFunctionField_ne_zero hne hp

private theorem coeffHom_injective_tc (x₀ : F) : Function.Injective (coeffHom x₀ H) := by
  have h1 : Function.Injective (Polynomial.coeToPowerSeries.ringHom (R := 𝕃 H)) := by
    intro a b hab
    apply Polynomial.coe_injective (𝕃 H)
    simpa [Polynomial.coeToPowerSeries.ringHom] using hab
  have h2 : Function.Injective ⇑(Polynomial.mapRingHom (liftToFunctionField (H := H))) := by
    rw [Polynomial.coe_mapRingHom]
    exact Polynomial.map_injective _ (liftToFunctionField_injective_tc H)
  have h3 : Function.Injective ⇑(Polynomial.taylorAlgHom (R := F[X]) (Polynomial.C x₀)).toRingHom := by
    intro a b hab
    apply Polynomial.taylor_injective (Polynomial.C x₀)
    have h : ∀ q : F[X][Y], (Polynomial.taylorAlgHom (R := F[X]) (Polynomial.C x₀)).toRingHom q
        = Polynomial.taylor (Polynomial.C x₀) q := fun q => by simp [Polynomial.taylorAlgHom_apply]
    rw [h, h] at hab; exact hab
  rw [coeffHom, RingHom.coe_comp, RingHom.coe_comp]
  exact h1.comp (h2.comp h3)

private theorem Q_natDegree_eq_tc (x₀ : F) (R : F[X][X][Y]) :
    (Q x₀ R H).natDegree = R.natDegree := by
  rw [Q, Polynomial.natDegree_map_eq_of_injective (coeffHom_injective_tc H x₀)]

/-! ### The two vanishing facts for the summand `f i`. -/

/-- The summand of the target Taylor sum. -/
private noncomputable def tcTerm (x₀ : F) (R : F[X][X][Y]) (i1 s i : ℕ) : 𝕃 H :=
  (i.choose s) • (liftToFunctionField (H:=H)
      ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i) * (α₀ H) ^ (i - s))

/-- Vanishing beyond `R.natDegree`: the `P₁`-coefficient is zero there. -/
private theorem tcTerm_eq_zero_of_natDegree_lt (x₀ : F) (R : F[X][X][Y]) (i1 s i : ℕ)
    (hi : R.natDegree < i) : tcTerm H x₀ R i1 s i = 0 := by
  rw [tcTerm]
  have hP1 : (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).natDegree ≤ R.natDegree := by
    have h1 : Bivariate.natDegreeY (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R))
        ≤ Bivariate.natDegreeY R :=
      (evalX_natDegreeY_le (Polynomial.C x₀) _).trans (hasseDerivX_natDegreeY_le i1 R)
    simpa [Bivariate.natDegreeY] using h1
  have hcoeff : (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  simp [hcoeff]

/-- Vanishing beyond `M + s` (`M` = natDegree of the `Δ_Y^s`-version): via the Hasse
commutation `evalX_hasseDeriv_Y_coeff`, the weighted coefficient is a lift of a zero coefficient. -/
private theorem tcTerm_eq_zero_of_M_lt (x₀ : F) (R : F[X][X][Y]) (i1 s i : ℕ)
    (hi : (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY s R))).natDegree + s < i) :
    tcTerm H x₀ R i1 s i = 0 := by
  rw [tcTerm]
  have hs : s ≤ i := by omega
  have hcomm := evalX_hasseDeriv_Y_coeff x₀ R i1 s (i - s)
  rw [Nat.sub_add_cancel hs] at hcomm
  have hMcoeff : (Bivariate.evalX (Polynomial.C x₀)
      (hasseDerivX i1 (hasseDerivY s R))).coeff (i - s) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hMcoeff] at hcomm
  rw [← smul_mul_assoc, ← map_nsmul (liftToFunctionField (H := H)), ← hcomm, map_zero, zero_mul]

/-! ### The base identity (brick1) for the `M+1+s` range. -/

private theorem taylorCollapse_baseRange (x₀ : F) (R : F[X][X][Y]) (i1 s : ℕ) :
    hasseEvalAtRoot H x₀ R i1 s
      = ∑ i ∈ Finset.range
          ((Bivariate.evalX (Polynomial.C x₀)
              (hasseDerivX i1 (hasseDerivY s R))).natDegree + 1 + s),
          tcTerm H x₀ R i1 s i := by
  simp only [tcTerm]
  rw [hasseEvalAtRoot_eq_taylorSum, α₀]
  symm
  set M := (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY s R))).natDegree with hM
  rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le s) (by omega : s ≤ M + 1 + s),
      Finset.sum_eq_zero (s := Finset.Ico 0 s) (fun i hi => by
        rw [Finset.mem_Ico] at hi
        rw [Nat.choose_eq_zero_of_lt hi.2, zero_smul]),
      zero_add, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr (by rw [Nat.add_sub_cancel])
  intro j _
  rw [Nat.add_sub_cancel_left, Nat.add_comm s j]

/-! ### MAIN: the `Q`-range version. -/

theorem taylorCollapse (x₀ : F) (R : F[X][X][Y]) (i1 s : ℕ) :
  ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
    (i.choose s) • (liftToFunctionField (H:=H)
        ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i) * (α₀ H) ^ (i - s))
  = hasseEvalAtRoot H x₀ R i1 s := by
  -- Fold the summand into `tcTerm` and replace `Q.natDegree` by `R.natDegree`.
  show ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1), tcTerm H x₀ R i1 s i = _
  rw [Q_natDegree_eq_tc]
  set M := (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY s R))).natDegree with hM
  -- Common superset `range K`, K = max (R.natDegree+1) (M+1+s).
  set K := max (R.natDegree + 1) (M + 1 + s) with hK
  -- Extend the R-range sum to range K (extra terms vanish by `tcTerm_eq_zero_of_natDegree_lt`).
  have hsubR : Finset.range (R.natDegree + 1) ⊆ Finset.range K :=
    Finset.range_mono (le_max_left (R.natDegree + 1) (M + 1 + s))
  have heqR : ∑ i ∈ Finset.range (R.natDegree + 1), tcTerm H x₀ R i1 s i
      = ∑ i ∈ Finset.range K, tcTerm H x₀ R i1 s i := by
    refine Finset.sum_subset hsubR (fun i _ hiR => ?_)
    rw [Finset.mem_range, not_lt] at hiR
    exact tcTerm_eq_zero_of_natDegree_lt H x₀ R i1 s i (by omega)
  -- Extend the M-range sum to range K (extra terms vanish by `tcTerm_eq_zero_of_M_lt`).
  have hsubM : Finset.range (M + 1 + s) ⊆ Finset.range K :=
    Finset.range_mono (le_max_right (R.natDegree + 1) (M + 1 + s))
  have heqM : ∑ i ∈ Finset.range (M + 1 + s), tcTerm H x₀ R i1 s i
      = ∑ i ∈ Finset.range K, tcTerm H x₀ R i1 s i := by
    refine Finset.sum_subset hsubM (fun i _ hiM => ?_)
    rw [Finset.mem_range, not_lt] at hiM
    exact tcTerm_eq_zero_of_M_lt H x₀ R i1 s i (by omega)
  rw [heqR, ← heqM, ← taylorCollapse_baseRange]

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.taylorCollapse
