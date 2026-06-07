on the genuine non-monic regime.

LEMMA A (`liftBivariate_eq_zero_of_natDegree_lt`): `liftBivariate` is injective on polynomials
of `Y`-degree `< H.natDegree`; such polynomials sit strictly below the modulus `H̃` so no
reduction occurs.  Proof: `liftBivariate q = 0 ↔ H̃ ∣ bivPolyHom q`; via `H_tilde_equiv_H_tilde'`
and `natDegree_H_tilde'`, the divisor has `Y`-degree `H.natDegree`, forcing the lower-degree `q`
to zero.

MAIN (`keystone_at_zero_FALSE`): combining the verified reduction `keystone_at_zero_iff_bare`
(d ≥ 2) with `W_pow_mul_eval₂_div_eq_liftBivariate`, keystone-at-0 becomes
`liftBivariate (cleared p) = liftBivariate p`, where `cleared p` rescales the `Y^i`-coefficient
of `p = evalX x₀ (Δ_X^1 R)` by `lc^{d-i}` (`d = R.natDegree`).  Then `cleared p - p` has
`Y`-degree `< d = H.natDegree` (its top coefficient `lc^0 - 1 = 0` cancels), so LEMMA A forces
`cleared p = p`.  But the `i₀`-coefficient is `p.coeff i₀ · (lc^{d-i₀} - 1) ≠ 0` whenever
`p.coeff i₀ ≠ 0` and `H` is non-monic (`lc` a non-unit, so `lc^{d-i₀} ≠ 1`).  Contradiction.
The defect is exactly the un-cleared `B_coeff` (it must use `hasseCoeffRepr𝒪_cleared`). -/

/-- LEMMA A. `liftBivariate` kills only the zero polynomial below `Y`-degree `H.natDegree`. -/
theorem liftBivariate_eq_zero_of_natDegree_lt {q : F[X][Y]}
    (hq : liftBivariate (H := H) q = 0) (hdeg : q.natDegree < H.natDegree) : q = 0 := by
  have hHdeg : 0 < H.natDegree := (‹Fact (0 < H.natDegree)›).out
  have hinj : Function.Injective (ToRatFunc.univPolyHom (F := F)) := by
    simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))
  -- liftBivariate q = 0  ↔  bivPolyHom q ∈ span {H_tilde H}
  have hmem : ToRatFunc.bivPolyHom q ∈ Ideal.span {H_tilde H} := by
    simp only [liftBivariate, RingHom.comp_apply] at hq
    rwa [Ideal.Quotient.eq_zero_iff_mem] at hq
  -- H_tilde H ∣ q.map univPolyHom, i.e. (H_tilde' H).map univPolyHom ∣ q.map univPolyHom
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

/-- THE DISPROOF: on the genuine non-monic regime, the order-0 keystone residual is FALSE,
so `RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0` cannot hold — the #139 keystone is unprovable
as stated.  `hlc : ¬ IsUnit H.leadingCoeff` encodes "`H` non-monic" (`W` a non-unit);
`hdeg : R.natDegree = H.natDegree` is the degree-preserving regime; `hp` says `p` has a genuine
sub-top `Y`-coefficient.  All three hold generically in Appendix A.4. -/
theorem keystone_at_zero_FALSE (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hdeg : R.natDegree = H.natDegree)
    (hlc : ¬ IsUnit H.leadingCoeff)
    (i₀ : ℕ) (hi₀ : i₀ < R.natDegree)
    (hp : (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i₀ ≠ 0) :
    ¬ RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 := by
  rw [keystone_at_zero_iff_bare H x₀ R hHyp hd]
  set p := Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R) with hpdef
  set d := R.natDegree with hddef
  have hpdeg : p.natDegree ≤ d := by
    calc p.natDegree = Bivariate.natDegreeY p := rfl
      _ ≤ Bivariate.natDegreeY (hasseDerivX 1 R) := evalX_natDegreeY_le _ _
      _ ≤ Bivariate.natDegreeY R := hasseDerivX_natDegreeY_le _ _
      _ = d := rfl
  intro hEq
  -- turn the LHS into liftBivariate of the cleared polynomial
  rw [α₀, mul_comm,
    W_pow_mul_eval₂_div_eq_liftBivariate (H := H) (P := p) (k := d) hpdeg] at hEq
  set clr : F[X][Y] := ∑ i ∈ Finset.range (d + 1),
    Polynomial.C (p.coeff i * H.leadingCoeff ^ (d - i)) * Polynomial.X ^ i with hclrdef
  -- liftBivariate (clr - p) = 0
  have hdiff : liftBivariate (H := H) (clr - p) = 0 := by rw [map_sub, hEq, sub_self]
  -- coefficientwise description of clr - p
  have clr_coeff : ∀ k, clr.coeff k =
      if k < d + 1 then p.coeff k * H.leadingCoeff ^ (d - k) else 0 := by
    intro k
    rw [hclrdef, Polynomial.finset_sum_coeff]
    simp_rw [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (Finset.range (d + 1)) k
        (fun i => p.coeff i * H.leadingCoeff ^ (d - i))]
    simp [Finset.mem_range]
  have diff_coeff : ∀ k, (clr - p).coeff k =
      if k < d + 1 then p.coeff k * (H.leadingCoeff ^ (d - k) - 1) else 0 := by
    intro k
    rw [Polynomial.coeff_sub, clr_coeff k]
    by_cases hk : k < d + 1
    · simp only [hk, if_true]; ring
    · simp only [hk, if_false, zero_sub]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < k), neg_zero]
  -- degree of clr - p is below H.natDegree = d
  have hdiffdeg : (clr - p).natDegree < H.natDegree := by
    have hle : (clr - p).natDegree ≤ d - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      rw [diff_coeff m]
      by_cases hk : m < d + 1
      · have hmd : m = d := by omega
        subst hmd; simp
      · simp [hk]
    omega
  have hzero := liftBivariate_eq_zero_of_natDegree_lt H hdiff hdiffdeg
  -- but the i₀-coefficient is nonzero
  have hci := diff_coeff i₀
  rw [hzero, Polynomial.coeff_zero, if_pos (by omega : i₀ < d + 1)] at hci
  refine (mul_ne_zero hp ?_) hci.symm
  intro hcontra
  have hpow : H.leadingCoeff ^ (d - i₀) = 1 := by rwa [sub_eq_zero] at hcontra
  have hposn : 1 ≤ d - i₀ := by omega
  exact hlc (IsUnit.of_mul_eq_one (H.leadingCoeff ^ (d - i₀ - 1)) (by
    rw [← pow_succ', Nat.sub_add_cancel hposn, hpow]))

