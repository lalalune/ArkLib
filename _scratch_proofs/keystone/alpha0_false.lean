import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight

open scoped BigOperators
open Polynomial Polynomial.Bivariate ToRatFunc BCIKS20AppendixA
open BCIKS20.HenselNumerator ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.AlphaWeightFalse

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## #138 PARALLEL DISPROOF — the P1 weight-1 base invariant is FALSE for non-monic `H`.

`AlphaGenuineRegularWeightLe_zero` asks for `a ∈ 𝒪` with `embedding a = αGenuine 0 = α₀ = T/W`.
But `embedding a = liftBivariate (canonicalRep a)` (Y-degree `< H.natDegree`), so the equation
`liftBivariate q = T/W` clears to `liftBivariate (q · C lc) = liftBivariate X`, and below the
modulus (LEMMA A) that forces `q · C lc = X` as polynomials — whose degree-1 coefficient gives
`q.coeff 1 · lc = 1`, i.e. `lc` a unit.  For non-monic `H` (`lc` not a unit, d ≥ 2) no such `a`
exists.  This is the **same un-cleared obstruction as #139**, now on the P1 side: `αGenuine` is
the un-cleared `T/W`; the genuine weight-1 element is the cleared `W·α₀ = T = Y_𝒪`. -/

/-- LEMMA A (re-proved standalone): `liftBivariate` injects below `Y`-degree `H.natDegree`. -/
theorem liftBivariate_eq_zero_of_natDegree_lt {q : F[X][Y]}
    (hq : liftBivariate (H := H) q = 0) (hdeg : q.natDegree < H.natDegree) : q = 0 := by
  have hHdeg : 0 < H.natDegree := (‹Fact (0 < H.natDegree)›).out
  have hinj : Function.Injective (ToRatFunc.univPolyHom (F := F)) := by
    simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))
  have hmem : ToRatFunc.bivPolyHom q ∈ Ideal.span {H_tilde H} := by
    simp only [liftBivariate, RingHom.comp_apply] at hq
    rwa [Ideal.Quotient.eq_zero_iff_mem] at hq
  have hdvd : (H_tilde' H).map (ToRatFunc.univPolyHom (F := F)) ∣
      q.map (ToRatFunc.univPolyHom (F := F)) := by
    rw [H_tilde_equiv_H_tilde']
    have := (Ideal.mem_span_singleton).1 hmem
    simpa [show ToRatFunc.bivPolyHom q = q.map (ToRatFunc.univPolyHom (F := F)) from rfl] using this
  by_contra hq0
  have hqmap0 : q.map (ToRatFunc.univPolyHom (F := F)) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero_iff hinj]
  have hle := Polynomial.natDegree_le_of_dvd hdvd hqmap0
  rw [Polynomial.natDegree_map_eq_of_injective hinj, Polynomial.natDegree_map_eq_of_injective hinj,
    natDegree_H_tilde' hHdeg] at hle
  omega

/-- THE #138 DISPROOF (stated against the inline existential — stronger than, and a fortiori
implying, `¬ AlphaGenuineRegularWeightLe_zero`, independent of repo def naming): for non-monic
`H` (d ≥ 2), **no** `𝒪`-element embeds to `αGenuine 0 = T/W` — regardless of weight. -/
theorem alphaWeight_zero_FALSE (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ H.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) :
    ¬ ∃ a : 𝒪 H, embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp 0 := by
  rintro ⟨a, ha_eq⟩
  have hHdeg : 0 < H.natDegree := by omega
  set q := canonicalRepOf𝒪 hHdeg a with hq
  have hemb : embeddingOf𝒪Into𝕃 H a = liftBivariate (H := H) q := by
    conv_lhs => rw [← mk_canonicalRepOf𝒪 hHdeg a]
    rw [embeddingOf𝒪Into𝕃_mk]
  rw [hemb, αGenuine_zero H x₀ R hHyp, α₀] at ha_eq
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hWdef
  have hWne : W ≠ 0 := liftToFunctionField_leadingCoeff_ne_zero (H := H)
  -- clear the denominator: liftBivariate (q · C lc) = liftBivariate X
  have key : liftBivariate (H := H) (q * Polynomial.C H.leadingCoeff)
      = liftBivariate (H := H) Polynomial.X := by
    rw [map_mul, liftBivariate_C, liftBivariate_X, ha_eq, div_mul_cancel₀ _ hWne]
  have hlc_ne : H.leadingCoeff ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.2
    intro h; rw [h, Polynomial.natDegree_zero] at hHdeg; omega
  have hqdeg : q.natDegree < H.natDegree := by
    rcases eq_or_ne q 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]; omega
    · have hdlt := canonicalRepOf𝒪_degree_lt hHdeg a
      have hHt : (H_tilde' H).degree = (H.natDegree : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree (H_tilde'_monic H hHdeg).ne_zero, natDegree_H_tilde' hHdeg]
      rw [hHt] at hdlt
      exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hdlt
  have hdeg : (q * Polynomial.C H.leadingCoeff - Polynomial.X).natDegree < H.natDegree := by
    apply lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
    rw [Polynomial.natDegree_mul_C hlc_ne, Polynomial.natDegree_X]
    exact max_lt hqdeg (by omega)
  have hzero : q * Polynomial.C H.leadingCoeff - Polynomial.X = 0 :=
    liftBivariate_eq_zero_of_natDegree_lt H (by rw [map_sub, key, sub_self]) hdeg
  have hc1 : (q * Polynomial.C H.leadingCoeff).coeff 1 = (Polynomial.X : F[X][Y]).coeff 1 := by
    rw [sub_eq_zero] at hzero; rw [hzero]
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_X_one] at hc1
  exact hlc (IsUnit.of_mul_eq_one (q.coeff 1) (by rw [mul_comm]; exact hc1))

/-- THE #138 FIX, VERIFIED: the *cleared* coefficient `W · αGenuine 0 = T` DOES have an
`𝒪`-witness of weight ≤ 1 — namely `βHensel 0 = mk X` (= `Y_𝒪`).  This is the corrected
weight-1 invariant; only the un-cleared `αGenuine` (`= T/W`) fails. -/
theorem alphaWeight_zero_FIXED (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ H.natDegree) (D : ℕ) (hD : D ≤ H.natDegree) :
    ∃ a : 𝒪 H,
      embeddingOf𝒪Into𝕃 H a
          = liftToFunctionField (H := H) H.leadingCoeff * αGenuine H x₀ R hHyp 0
        ∧ weight_Λ_over_𝒪 (show 0 < H.natDegree by omega) a D ≤ (WithBot.some 1 : WithBot ℕ) := by
  have hHdeg : 0 < H.natDegree := by omega
  have hW : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  refine ⟨βHensel H x₀ R hHyp 0, ?_, ?_⟩
  · rw [embeddingOf𝒪Into𝕃_βHensel_zero, αGenuine_zero, α₀]
    field_simp
  · have hdeglt : (Polynomial.X : F[X][Y]).degree < (H_tilde' H).degree := by
      rw [Polynomial.degree_X, Polynomial.degree_eq_natDegree (H_tilde'_monic H hHdeg).ne_zero,
        natDegree_H_tilde' hHdeg]
      exact_mod_cast (by omega : (1 : ℕ) < H.natDegree)
    rw [weight_Λ_over_𝒪, βHensel_zero, canonicalRepOf𝒪_mk_eq_self_of_degree_lt hHdeg hdeglt]
    calc weight_Λ (Polynomial.X : F[X][Y]) H D
          = weight_Λ ((Polynomial.X : F[X][Y]) ^ 1) H D := by rw [pow_one]
      _ ≤ (WithBot.some (1 * (D + 1 - Bivariate.natDegreeY H)) : WithBot ℕ) :=
          weight_Λ_X_pow_le H D 1
      _ ≤ (WithBot.some 1 : WithBot ℕ) := by
          apply WithBot.coe_le_coe.2
          have hnd : Bivariate.natDegreeY H = H.natDegree := rfl
          rw [hnd, one_mul]; omega

/-- COROLLARY (all-orders): the FULL P1 regularity invariant `∀ t, ∃ a ∈ 𝒪, embedding a =
αGenuine t` is false for non-monic `H` — it demands its (false) `t = 0` instance.  Hence
`AlphaGenuineRegularWeightLe` (which adds a weight bound on top) is false a fortiori. -/
theorem alphaWeight_ALL_FALSE (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ H.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) :
    ¬ ∀ t : ℕ, ∃ a : 𝒪 H, embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp t := by
  intro h
  exact alphaWeight_zero_FALSE H x₀ R hHyp hd hlc (h 0)

end BCIKS20.AlphaWeightFalse

section Audit
open BCIKS20.AlphaWeightFalse
#print axioms alphaWeight_zero_FALSE
#print axioms alphaWeight_zero_FIXED
#print axioms alphaWeight_ALL_FALSE
end Audit
