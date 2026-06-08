import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator.AlphaWeight

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! # The Sharp Divisibility Obstruction for Non-Monic `H`

The `AlphaGenuineRegularWeightLe` and `DivWeightLe` invariants assert that `W𝒪 ∣ βHensel 0`
in `𝒪 H`. As `W𝒪 = mk (C (lc H))`, this divisibility requires `lc H ∣ X` in `F[X]`.
We prove this impossibility outright, confirming the author's note that the unresummed
invariant is provably false for general non-monic `H`.
-/

theorem not_DivWeightLe_zero_of_not_dvd_X (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree) (h_not_dvd : ¬ H.leadingCoeff ∣ Polynomial.X) :
    ¬ DivWeightLe_zero H x₀ R hHyp hH D := by
  rintro ⟨a, hEq, _⟩
  have hEq2 : βHensel H x₀ R hHyp 0 = a * W𝒪 H := by simpa using hEq
  rw [βHensel_zero] at hEq2
  set A := canonicalRepOf𝒪 hH a with hA
  have hA_mk : Ideal.Quotient.mk (Ideal.span {H_tilde' H}) A = a := mk_canonicalRepOf𝒪 hH a
  have hW_mk : W𝒪 H = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C H.leadingCoeff) := rfl
  have hmk_eq : Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.X : F[X][Y]) = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (A * Polynomial.C H.leadingCoeff) := by
    rw [hEq2, ← hA_mk, hW_mk, ← map_mul]
  have hdif : Ideal.Quotient.mk (Ideal.span {H_tilde' H}) ((Polynomial.X : F[X][Y]) - A * Polynomial.C H.leadingCoeff) = 0 := by
    rw [map_sub, hmk_eq, sub_self]
  have hdegX : (Polynomial.X : F[X][Y]).degree < (H_tilde' H).degree := by
    rw [Polynomial.degree_X, Polynomial.degree_eq_natDegree (H_tilde'_monic H hH).ne_zero, natDegree_H_tilde' hH]
    exact_mod_cast (by omega)
  have hdegA : A.degree < (H_tilde' H).degree := canonicalRepOf𝒪_degree_lt hH a
  have hdegC : (Polynomial.C H.leadingCoeff).degree ≤ 0 := Polynomial.degree_C_le
  have hdegAC : (A * Polynomial.C H.leadingCoeff).degree < (H_tilde' H).degree := by
    refine (Polynomial.degree_mul_le _ _).trans_lt ?_
    exact lt_of_le_of_lt (add_le_add_left hdegC _) (by simpa using hdegA)
  have hdeg_sub : ((Polynomial.X : F[X][Y]) - A * Polynomial.C H.leadingCoeff).degree < (H_tilde' H).degree := by
    refine (Polynomial.degree_sub_le _ _).trans_lt ?_
    exact max_lt hdegX hdegAC
  have h_eq_zero : (Polynomial.X : F[X][Y]) - A * Polynomial.C H.leadingCoeff = 0 := by
    have h_can := canonicalRepOf𝒪_mk_eq_self_of_degree_lt hH hdeg_sub
    rw [hdif, canonicalRepOf𝒪_zero hH] at h_can
    exact h_can.symm
  have h_X_eq : (Polynomial.X : F[X][Y]) = A * Polynomial.C H.leadingCoeff := sub_eq_zero.mp h_eq_zero
  -- (Polynomial.X : F[X][Y]) is actually the variable Y in F[X][Y]
  -- We extract the Y-coefficient of both sides.
  have h_coeff : (Polynomial.X : F[X][Y]).coeff 1 = (A * Polynomial.C H.leadingCoeff).coeff 1 := by rw [h_X_eq]
  rw [Polynomial.coeff_X_one] at h_coeff
  rw [Polynomial.coeff_mul_C] at h_coeff
  have h_div_one : H.leadingCoeff ∣ 1 := ⟨A.coeff 1, h_coeff.symm⟩
  apply h_not_dvd
  exact dvd_trans h_div_one (one_dvd Polynomial.X)

end BCIKS20.HenselNumerator.AlphaWeight
