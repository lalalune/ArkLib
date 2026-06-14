/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
#389 residual `alphagenuine-regular-weightle`.

The residual `AlphaGenuineRegularWeightLe` is FALSE-as-stated (already refuted axiom-clean,
`not_alphaGenuineRegularWeightLe`). The actionable target is the CLEARED monic successor core,
isolated in `P1MonicWeightExplicit.lean` to a single explicit element:

    ∀ t, weight_Λ_over_𝒪 hH (henselQuotient t) D ≤ 1.

The t=0 face is proven on ONE good instance (`WeightWitness.weight_holds`, K = ZMod 3) and
refuted on one bad instance (`WeightWitness.weight_refuted`). This file GENERALIZES the
good-instance argument to a reusable, instance-free bridge over ARBITRARY monic separable H:
a reduced ξ-clearing witness for `βHensel 1` of weight ≤ 1 discharges the t=0 monic weight core.
This converts `weight_holds`'s inlined computation into a general theorem and pins the exact
remaining obstruction (constructing such a witness = inverting ξ in 𝒪 while controlling the
representative degree = the Newton-cancellation wall).
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1MonicWeightExplicit
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1MonicWeightHolds

open Polynomial Polynomial.Bivariate BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **General monic t=0 succ-weight bridge (the reusable form of `weight_holds`).**
For monic `H`, if there is a *reduced* polynomial witness `w` (below the modulus, of `Λ`-weight
`≤ 1`) clearing `βHensel 1` by `ξ` in `𝒪 H` (i.e. `mk w · ξ = βHensel 1`), then the explicit
quotient `henselQuotient 0` has `Λ_𝒪`-weight `≤ 1`. Because `ξ` is a unit
(`isUnit_ξ_of_monic`), the witness `mk w` is forced equal to `henselQuotient 0`, so the bound
transports directly. No instance-specific data; works for every monic separable `ClaimA2`
input. -/
theorem henselQuotient_zero_weight_le_one_of_reduced_witness
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1) {D : ℕ} (w : F[X][Y])
    (hwdeg : w.degree < (H_tilde' H).degree)
    (hwwt : weight_Λ w H D ≤ WithBot.some 1)
    (hclear : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) w : 𝒪 H)
        * ClaimA2.ξ x₀ R H hHyp = βHensel H x₀ R hHyp 1) :
    weight_Λ_over_𝒪 hH (henselQuotient H x₀ R hHyp hlc 0) D ≤ WithBot.some 1 := by
  -- ξ is a unit, so the clearing witness `mk w` is forced equal to `henselQuotient 0`.
  have hv : IsUnit (ClaimA2.ξ x₀ R H hHyp) := isUnit_ξ_of_monic H x₀ R hHyp hlc
  -- `henselQuotient 0 · ξ^(2·0+1) = βHensel 1`, and `ξ^(2·0+1) = ξ`.
  have hHQ : henselQuotient H x₀ R hHyp hlc 0 * ClaimA2.ξ x₀ R H hHyp
      = βHensel H x₀ R hHyp 1 := by
    have h := henselQuotient_mul_xi H x₀ R hHyp hlc 0
    simpa using h
  -- Cancel the unit ξ.
  have heq : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) w : 𝒪 H)
      = henselQuotient H x₀ R hHyp hlc 0 := by
    apply hv.mul_left_inj.mp
    rw [hclear, hHQ]
  -- Transport the reduced-representative weight.
  rw [← heq, weight_Λ_over_𝒪_mk_eq_self_of_degree_lt hH hwdeg]
  exact hwwt

/-- **The t=0 case of `SuccDivWeightLe_of_monic`'s existential, from a reduced witness.**
A reduced ξ-clearing witness `w` of weight `≤ 1` directly supplies the order-0 successor
divisibility-with-weight existential `∃ a, βHensel 1 = a·ξ^(2·0+1) ∧ Λ_𝒪(a) ≤ 1`. This is the
single open conjunct of the monic P1 invariant at order 0, discharged from the polynomial-level
data `w`. -/
theorem succDivWeight_monic_zero_of_reduced_witness
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (w : F[X][Y])
    (hwdeg : w.degree < (H_tilde' H).degree)
    (hwwt : weight_Λ w H D ≤ WithBot.some 1)
    (hclear : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) w : 𝒪 H)
        * ClaimA2.ξ x₀ R H hHyp = βHensel H x₀ R hHyp 1) :
    ∃ a : 𝒪 H, βHensel H x₀ R hHyp (0 + 1)
        = a * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * 0 + 1)
      ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 := by
  refine ⟨Ideal.Quotient.mk (Ideal.span {H_tilde' H}) w, ?_, ?_⟩
  · simpa using hclear.symm
  · rw [weight_Λ_over_𝒪_mk_eq_self_of_degree_lt hH hwdeg]
    exact hwwt

/-- **Concrete-closed-form refinement.** The clearing hypothesis of the bridge, expressed
through the proven closed form `βHensel 1 = − hasseCoeffRepr𝒪(R, 1, 0)`. The caller now only has
to exhibit a reduced weight-`≤ 1` polynomial `w` with `mk w · ξ = − hasseCoeffRepr𝒪(R, 1, 0)` (a
concrete `𝒪`-equation in the order-1 lift coefficient), and the t=0 monic henselQuotient weight
core follows. This is the exact, instance-free shape of the BCIKS20 A.4 order-1 weight claim. -/
theorem henselQuotient_zero_weight_le_one_of_clears_hasse
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1) {D : ℕ} (w : F[X][Y])
    (hwdeg : w.degree < (H_tilde' H).degree)
    (hwwt : weight_Λ w H D ≤ WithBot.some 1)
    (hclear : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) w : 𝒪 H)
        * ClaimA2.ξ x₀ R H hHyp = - hasseCoeffRepr𝒪 H x₀ R 1 0) :
    weight_Λ_over_𝒪 hH (henselQuotient H x₀ R hHyp hlc 0) D ≤ WithBot.some 1 := by
  refine henselQuotient_zero_weight_le_one_of_reduced_witness
    H x₀ R hHyp hH hlc w hwdeg hwwt ?_
  rw [hclear, ← βHensel_one_eq H x₀ R hHyp]

end BCIKS20.HenselNumerator

/-! ## Faithfulness / non-vacuity check: the bridge SUBSUMES the good instance.

We re-derive the proven good-instance result `WeightWitness.weight_holds`
(`R = Y²−2+u` over `ZMod 3`) — but now as the `henselQuotient`-form t=0 weight core — by
feeding the general bridge `henselQuotient_zero_weight_le_one_of_reduced_witness` with the
witness `w = monomial 1 (−1)`. This confirms the generalization is faithful and non-vacuous:
the instance is a special case of the general theorem. -/
namespace BCIKS20.HenselNumerator.WeightWitness

open BCIKS20.HenselNumerator

/-- On the good instance `R = Y²−2+u`, the t=0 monic henselQuotient weight core
`Λ_𝒪(henselQuotient 0) ≤ 1` holds — derived through the GENERAL bridge, not by re-inlining the
instance computation. Witnesses the bridge subsumes `weight_holds`. -/
theorem henselQuotient_zero_weight_holds_good_instance (hH : 0 < myH.natDegree) :
    weight_Λ_over_𝒪 hH
        (henselQuotient myH 0 myRG myHypG myH_leadingCoeff 0) 2 ≤ WithBot.some 1 := by
  -- `weight_holds` supplies a witness `a` with `βHensel 1 = a·ξ` and `Λ_𝒪(a) ≤ 1`.
  -- Since ξ is a unit, that `a` is forced equal to `henselQuotient 0`, so its weight transports.
  obtain ⟨a, ha_eq, ha_wt⟩ := weight_holds hH
  have hv : IsUnit (ClaimA2.ξ 0 myRG myH myHypG) :=
    isUnit_ξ_of_monic myH 0 myRG myHypG myH_leadingCoeff
  have hHQ : henselQuotient myH 0 myRG myHypG myH_leadingCoeff 0
      * ClaimA2.ξ 0 myRG myH myHypG = βHensel myH 0 myRG myHypG 1 := by
    simpa using henselQuotient_mul_xi myH 0 myRG myHypG myH_leadingCoeff 0
  have ha : a = henselQuotient myH 0 myRG myHypG myH_leadingCoeff 0 := by
    apply hv.mul_left_inj.mp
    rw [← ha_eq, hHQ]
  rw [← ha]; exact ha_wt

end BCIKS20.HenselNumerator.WeightWitness
