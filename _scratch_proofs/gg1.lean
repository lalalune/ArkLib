import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Match

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine
open ProximityPrize.HenselSeriesCoeff

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The t-truncation of gammaGenuine: a power series agreeing with gammaGenuine below t+1. -/
noncomputable def ggTrunc (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) : PowerSeries (𝕃 H) :=
  PowerSeries.mk (fun j =>
    if j ≤ t then PowerSeries.coeff j (gammaGenuine x₀ R H hHyp) else 0)

/-- The Newton trunc-defect recursion for gammaGenuine (the analog of
`coeff_succ_eval_defect_reduction`). -/
theorem gg_defect_reduction (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    PowerSeries.coeff (t + 1) (Polynomial.eval (gammaGenuine x₀ R H hHyp) (Q x₀ R H)) =
      PowerSeries.coeff (t + 1) (Polynomial.eval (ggTrunc H x₀ R hHyp t) (Q x₀ R H))
        + ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) (gammaGenuine x₀ R H hHyp) := by
  have hagree : ∀ j < t + 1,
      PowerSeries.coeff j (gammaGenuine x₀ R H hHyp)
        = PowerSeries.coeff j (ggTrunc H x₀ R hHyp t) := by
    intro j hj
    simp only [ggTrunc, PowerSeries.coeff_mk, if_pos (Nat.lt_succ_iff.mp hj)]
  have hsub := ProximityPrize.HenselSeriesCoeff.coeff_eval_sub_at (Q := Q x₀ R H)
    (γ₁ := gammaGenuine x₀ R H hHyp) (γ₂ := ggTrunc H x₀ R hHyp t)
    (Nat.succ_pos t) hagree
  have htrunc_top : PowerSeries.coeff (t + 1) (ggTrunc H x₀ R hHyp t) = 0 := by
    simp only [ggTrunc, PowerSeries.coeff_mk, if_neg (by omega : ¬ t + 1 ≤ t)]
  have hderiv : Polynomial.eval (PowerSeries.constantCoeff (gammaGenuine x₀ R H hHyp))
      (Polynomial.derivative (ProximityPrize.HenselSeriesCoeff.Q₀ (Q x₀ R H)))
        = ClaimA2.ζ R x₀ H := by
    rw [gammaGenuine_constantCoeff, eval_α₀_derivative_Q₀]
  rw [htrunc_top, sub_zero, hderiv] at hsub
  linear_combination hsub

/-- ggTrunc and βHenselTrunc agree when βHA and gammaGenuine agree below t+1. -/
theorem trunc_eq_of_agree (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) (hIH : ∀ j ≤ t, PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp)
      = PowerSeries.coeff j (gammaGenuine x₀ R H hHyp)) :
    βHenselTrunc H x₀ R hHyp t = ggTrunc H x₀ R hHyp t := by
  ext j
  simp only [βHenselTrunc, ggTrunc, PowerSeries.coeff_mk]
  by_cases hj : j ≤ t
  · rw [if_pos hj, if_pos hj, hIH j hj]
  · rw [if_neg hj, if_neg hj]

/-- **KEY REDUCTION (Route 1):** the inductive step `coeff(t+1) βHA = coeff(t+1) gammaGenuine`,
given agreement below t+1, is EQUIVALENT to the per-order root vanishing
`coeff(t+1)(eval βHA Q) = 0`. -/
theorem step_iff_root_vanish (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) (hIH : ∀ j ≤ t, PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp)
      = PowerSeries.coeff j (gammaGenuine x₀ R H hHyp)) :
    PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
        = PowerSeries.coeff (t + 1) (gammaGenuine x₀ R H hHyp)
    ↔ PowerSeries.coeff (t + 1) (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) = 0 := by
  have hβ := coeff_succ_eval_defect_reduction H x₀ R hHyp t
  have hg := gg_defect_reduction H x₀ R hHyp t
  rw [gammaGenuine_root hHyp] at hg
  simp only [map_zero] at hg
  have htr := trunc_eq_of_agree H x₀ R hHyp t hIH
  rw [htr] at hβ
  have hζ : ClaimA2.ζ R x₀ H ≠ 0 := ζ_ne_zero H x₀ R hHyp
  constructor
  · intro heq
    rw [heq] at hβ
    linear_combination hβ - hg
  · intro hroot
    rw [hroot] at hβ
    have : ClaimA2.ζ R x₀ H * (PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
        - PowerSeries.coeff (t + 1) (gammaGenuine x₀ R H hHyp)) = 0 := by
      linear_combination hg - hβ
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hζ
    · linear_combination h

end BCIKS20.HenselNumerator

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Route-1 strong-induction skeleton (PROVEN reduction).**  If the per-order root vanishing
holds for every `t` (the keystone residual, form B), then `βHA` and `gammaGenuine` agree at every
coefficient — by strong induction whose step is EXACTLY `step_iff_root_vanish`.  This makes the
Route-1 dependency on the keystone fully explicit and sorry-free as a reduction. -/
theorem coeff_eq_of_root_vanish (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hvan : ∀ t : ℕ,
      PowerSeries.coeff (t + 1) (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) = 0)
    (n : ℕ) :
    PowerSeries.coeff n (βHenselAssembled H x₀ R hHyp)
      = PowerSeries.coeff n (gammaGenuine x₀ R H hHyp) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_zero_eq_constantCoeff_apply,
        βHenselAssembled_constantCoeff, gammaGenuine_constantCoeff]
    | (t + 1) =>
      have hIH : ∀ j ≤ t, PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp)
          = PowerSeries.coeff j (gammaGenuine x₀ R H hHyp) :=
        fun j hj => ih j (by omega)
      exact (step_iff_root_vanish H x₀ R hHyp t hIH).mpr (hvan t)

/-- **Route-1 closes `βHA = gammaGenuine` from the keystone (PROVEN reduction).** -/
theorem βHenselAssembled_eq_gammaGenuine_of_root_vanish (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hvan : ∀ t : ℕ,
      PowerSeries.coeff (t + 1) (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) = 0) :
    βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp := by
  ext n
  exact coeff_eq_of_root_vanish H x₀ R hHyp hvan n

/-- **The clean keystone equivalence (form C ⟺ form B), PROVEN both directions.**
`βHA = gammaGenuine` iff the per-order root vanishing holds.  Forward: `gammaGenuine` is the root
and equality transports vanishing; backward: the Route-1 strong induction. -/
theorem βHenselAssembled_eq_gammaGenuine_iff_root_vanish (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp
    ↔ ∀ t : ℕ,
        PowerSeries.coeff (t + 1)
          (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) = 0 := by
  constructor
  · intro heq t
    rw [heq, gammaGenuine_root hHyp, map_zero]
  · exact βHenselAssembled_eq_gammaGenuine_of_root_vanish H x₀ R hHyp

end BCIKS20.HenselNumerator

-- Axiom audit: confirm sorry-free.
section Audit
open BCIKS20.HenselNumerator
#print axioms gg_defect_reduction
#print axioms trunc_eq_of_agree
#print axioms step_iff_root_vanish
#print axioms coeff_eq_of_root_vanish
#print axioms βHenselAssembled_eq_gammaGenuine_of_root_vanish
#print axioms βHenselAssembled_eq_gammaGenuine_iff_root_vanish
end Audit
