import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Reabsorb
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Vanish

/-!
Route 1+3 made rigorous: the strong-induction skeleton, isolating EXACTLY the residual.

Key non-circular fact: gammaGenuine is a proven root, so its truncated-defect identity holds.
We show that IF βHA satisfies the SAME truncated-defect cancellation as gammaGenuine does (i.e.
the A.1 recursion = Newton step), THEN βHA = gammaGenuine.  This re-derives the equivalence and
confirms the residual is precisely the per-order recursion match — no shortcut via uniqueness.
-/

noncomputable section

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- gammaGenuine's own truncated-defect identity, derived from `gammaGenuine_root` + the Newton
split applied to gammaGenuine.  This is the analogue of `coeff_succ_eval_defect_reduction` but for
gammaGenuine, and it shows the truncated defect of gammaGenuine equals `-ζ·coeff(t+1)(gammaGenuine)`. -/
theorem gammaGenuine_trunc_defect (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval
          (PowerSeries.mk (fun j => if j ≤ t then PowerSeries.coeff j (gammaGenuine x₀ R H hHyp)
                                    else 0)) (Q x₀ R H))
      + ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) (gammaGenuine x₀ R H hHyp) = 0 := by
  -- Newton split for gammaGenuine against its own truncation:
  set γ := gammaGenuine x₀ R H hHyp with hγ
  set γt : PowerSeries (𝕃 H) :=
    PowerSeries.mk (fun j => if j ≤ t then PowerSeries.coeff j γ else 0) with hγt
  have hagree : ∀ j < t + 1, PowerSeries.coeff j γ = PowerSeries.coeff j γt := by
    intro j hj
    rw [hγt, PowerSeries.coeff_mk, if_pos (Nat.lt_succ_iff.mp hj)]
  have hsub := ProximityPrize.HenselSeriesCoeff.coeff_eval_sub_at (Q := Q x₀ R H)
    (γ₁ := γ) (γ₂ := γt) (Nat.succ_pos t) hagree
  have htrunc_top : PowerSeries.coeff (t + 1) γt = 0 := by
    rw [hγt, PowerSeries.coeff_mk, if_neg (by omega)]
  have hderiv : Polynomial.eval (PowerSeries.constantCoeff γ)
      (Polynomial.derivative (ProximityPrize.HenselSeriesCoeff.Q₀ (Q x₀ R H)))
        = ClaimA2.ζ R x₀ H := by
    rw [hγ, gammaGenuine_constantCoeff hHyp, eval_α₀_derivative_Q₀]
  rw [htrunc_top, sub_zero, hderiv] at hsub
  -- eval γ Q = 0 (gammaGenuine is a root)
  have hroot : PowerSeries.coeff (t + 1) (Polynomial.eval γ (Q x₀ R H)) = 0 := by
    rw [hγ, gammaGenuine_root hHyp]; simp
  rw [hroot] at hsub
  linear_combination -hsub

/-- **Self-contained strong-induction proof that the per-order recursion match is EXACTLY the
residual.**  If `βHA` satisfies the same truncated-defect cancellation that `gammaGenuine`
provably does (i.e. the A.1 recursion reproduces the Newton step at every order), then every
coefficient of `βHA` equals the corresponding coefficient of `gammaGenuine`.  This isolates the
keystone to the per-order recursion match and confirms it is genuinely non-circular: the ONLY
missing fact is that βHA's A.1 step equals the Newton step.  (gammaGenuine's step is a theorem;
βHA's is the open content.) -/
theorem coeff_βHA_eq_gammaGenuine_of_match (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : ∀ t : ℕ,
      PowerSeries.coeff (t + 1)
          (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
        + ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp) = 0)
    (n : ℕ) :
    PowerSeries.coeff n (βHenselAssembled H x₀ R hHyp)
      = PowerSeries.coeff n (gammaGenuine x₀ R H hHyp) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | t
    · -- base case n = 0: both constant coeffs are α₀.
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_zero_eq_constantCoeff_apply,
        βHenselAssembled_constantCoeff, gammaGenuine_constantCoeff hHyp]
    · -- step case n = t+1.
      -- ζ is a unit (nonzero in the field), so it suffices to show ζ·coeff(t+1)βHA = ζ·coeff(t+1)γ.
      have hζ : ClaimA2.ζ R x₀ H ≠ 0 := ζ_ne_zero H x₀ R hHyp
      -- truncations agree because all lower coeffs agree (IH below t+1):
      have hbelow : ∀ j ≤ t, PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp)
          = PowerSeries.coeff j (gammaGenuine x₀ R H hHyp) := fun j hj => ih j (by omega)
      -- βHenselTrunc t = gammaGenuine-truncation (coefficients ≤ t agree, both 0 above t).
      have htrunc_eq : βHenselTrunc H x₀ R hHyp t
          = PowerSeries.mk (fun j => if j ≤ t then PowerSeries.coeff j (gammaGenuine x₀ R H hHyp)
                                     else 0) := by
        ext j
        rw [βHenselTrunc, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
        by_cases hj : j ≤ t
        · rw [if_pos hj, if_pos hj, hbelow j hj]
        · rw [if_neg hj, if_neg hj]
      -- βHA's defect cancellation (hypothesis) and γ's defect cancellation (proven), with equal
      -- truncated defects.
      have hβ := hmatch t
      have hγ := gammaGenuine_trunc_defect H x₀ R hHyp t
      rw [htrunc_eq] at hβ
      -- subtract: ζ·(coeff(t+1)βHA - coeff(t+1)γ) = 0.
      have key : ClaimA2.ζ R x₀ H *
          (PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
            - PowerSeries.coeff (t + 1) (gammaGenuine x₀ R H hHyp)) = 0 := by
        linear_combination hβ - hγ
      rcases mul_eq_zero.mp key with h | h
      · exact absurd h hζ
      · exact sub_eq_zero.mp h

/-- The clean endpoint: βHA = gammaGenuine from the per-order recursion match (self-contained). -/
theorem βHA_eq_gammaGenuine_of_match (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : ∀ t : ℕ,
      PowerSeries.coeff (t + 1)
          (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
        + ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp) = 0) :
    βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp :=
  PowerSeries.ext (coeff_βHA_eq_gammaGenuine_of_match H x₀ R hHyp hmatch)

end BCIKS20.HenselNumerator

-- Axiom audit
#print axioms BCIKS20.HenselNumerator.gammaGenuine_trunc_defect
#print axioms BCIKS20.HenselNumerator.coeff_βHA_eq_gammaGenuine_of_match
#print axioms BCIKS20.HenselNumerator.βHA_eq_gammaGenuine_of_match
