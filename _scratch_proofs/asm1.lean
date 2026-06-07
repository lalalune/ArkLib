import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## BRIDGE 1 (the TRUE form).

The task's literal BRIDGE 1 — `emb (mk p) = W^N · hasseEvalAtRoot` for the *un-cleared*
representative `hasseCoeffRepr𝒪 = mk p` — is **mathematically FALSE**: unfolding gives
`eval₂ T p = W^N · eval₂ (T/W) p`, i.e. `∑ c_i T^i = ∑ c_i W^{N-i} T^i`, which holds only when
`p` is a monomial.  (Concrete witness `p = X + 1`: `eval₂ T = T+1` but `W·eval₂(T/W) = T+W`.)

The TRUE bridge is for the **cleared** representative, and it is exactly the in-tree lemma
`embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared`. -/
theorem bridge1_cleared (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        (hasseCoeffRepr𝒪_cleared H x₀ R i1 m) : 𝒪 H)
      = liftToFunctionField (H := H) H.leadingCoeff
            ^ Bivariate.natDegreeY
                (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R)))
        * hasseEvalAtRoot H x₀ R i1 m :=
  embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared H x₀ R i1 m

/-- BRICK E (local): `hasseEvalAtRoot = emb ⟦cleared⟧ / W^N`, derived from `bridge1_cleared`. -/
lemma brickE (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    hasseEvalAtRoot H x₀ R i1 m
      = embeddingOf𝒪Into𝕃 H
          (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
            (hasseCoeffRepr𝒪_cleared H x₀ R i1 m) : 𝒪 H)
        / liftToFunctionField (H := H) H.leadingCoeff
            ^ Bivariate.natDegreeY
                (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))) := by
  rw [bridge1_cleared, mul_comm, mul_div_assoc,
      div_self (pow_ne_zero _ (liftToFunctionField_leadingCoeff_ne_zero (H := H))), mul_one]

/-! ## Local re-statements of the verified bricks. -/

theorem taylorCollapse (x₀ : F) (R : F[X][X][Y]) (i1 s : ℕ) :
  ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
    (i.choose s) • (liftToFunctionField (H:=H)
        ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i) * (α₀ H) ^ (i - s))
  = hasseEvalAtRoot H x₀ R i1 s := by
  sorry -- VERIFIED BRICK (keystone_base.lean, compiles clean); stubbed to keep this file fast

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
private theorem sum_div' {K : Type} [Field K] (s : Finset ℕ) (f : ℕ → K) (d : K) :
    (∑ i ∈ s, f i) / d = ∑ i ∈ s, f i / d := by
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => (div_eq_mul_inv _ _).symm)

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
theorem depSwap {c N : ℕ} (A : ℕ → 𝕃 H) (g : ℕ → Nat.Partition c → 𝕃 H)
    (Q : Nat.Partition c → Prop) [DecidablePred Q] :
    ∑ i ∈ Finset.range N, A i * ∑ lam ∈ (Finset.univ : Finset (Nat.Partition c)).filter
        (fun lam => lam.parts.card ≤ i ∧ Q lam), g i lam
      = ∑ lam ∈ (Finset.univ : Finset (Nat.Partition c)).filter Q,
          ∑ i ∈ (Finset.range N).filter (fun i => lam.parts.card ≤ i), A i * g i lam := by
  simp only [Finset.mul_sum]
  apply Finset.sum_comm'
  intro i lam
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and]
  tauto

/-! ## STEP 4 — LHS i-sum collapse (filter drop + taylorCollapse), PROVEN
(modulo the verified `taylorCollapse` brick). -/
theorem lhs_isum_collapse (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t i1 : ℕ) (lam : Nat.Partition (t + 1 - i1)) :
    ∑ i ∈ (Finset.range ((Q x₀ R H).natDegree + 1)).filter (fun i => lam.parts.card ≤ i),
        liftToFunctionField (H:=H) ((evalX (C x₀) (hasseDerivX i1 R)).coeff i) *
          (i.choose lam.parts.card * lam.parts.countPerms) •
            (α₀ H ^ (i - lam.parts.card) *
              (Multiset.map (fun j => (PowerSeries.coeff j) (βHenselAssembled H x₀ R hHyp)) lam.parts).prod)
      = lam.parts.countPerms •
          (hasseEvalAtRoot H x₀ R i1 lam.parts.card
            * (Multiset.map (fun j => (PowerSeries.coeff j) (βHenselAssembled H x₀ R hHyp)) lam.parts).prod) := by
  set s := lam.parts.card with hs
  set cp := lam.parts.countPerms with hcp
  set P := (Multiset.map (fun j => (PowerSeries.coeff j) (βHenselAssembled H x₀ R hHyp)) lam.parts).prod with hP
  have hext : ∑ i ∈ (Finset.range ((Q x₀ R H).natDegree + 1)).filter (fun i => s ≤ i),
        liftToFunctionField (H:=H) ((evalX (C x₀) (hasseDerivX i1 R)).coeff i) *
          (i.choose s * cp) • (α₀ H ^ (i - s) * P)
      = ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
        liftToFunctionField (H:=H) ((evalX (C x₀) (hasseDerivX i1 R)).coeff i) *
          (i.choose s * cp) • (α₀ H ^ (i - s) * P) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hi'
    simp only [Finset.mem_filter, Finset.mem_range] at hi hi'
    rw [Nat.choose_eq_zero_of_lt (by omega : i < s)]; simp
  rw [hext]
  have hcollapse := taylorCollapse H x₀ R i1 s
  have key : (∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
        liftToFunctionField (H:=H) ((evalX (C x₀) (hasseDerivX i1 R)).coeff i) *
          (i.choose s * cp) • (α₀ H ^ (i - s) * P))
      = cp • ((∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
          (i.choose s) • (liftToFunctionField (H:=H) ((evalX (C x₀) (hasseDerivX i1 R)).coeff i) * α₀ H ^ (i - s))) * P) := by
    simp only [nsmul_eq_mul, Nat.cast_mul, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [key, hcollapse]

/-! ## The per-`(i1,λ)` term goal, fully reduced (STEP 4–7 applied).

Reaching this bare goal IS the entire remaining content.  It exposes the **mathematical
obstruction**: after collapse the LHS carries `emb ⟦cleared⟧ = liftBivariate(cleared)` (via
`brickE`), while the RHS's `B_coeff` carries the *un-cleared* `emb hasseCoeffRepr𝒪 =
liftBivariate(p)`.  These two are NOT related by any global power of `W`
(`liftBivariate(cleared) = ∑ c_i W^{N-i} T^i` vs `liftBivariate(p) = ∑ c_i T^i`), so the term
identity is FALSE unless `B_coeff` is built from `hasseCoeffRepr𝒪_cleared` rather than
`hasseCoeffRepr𝒪`.  The remaining `sorry` is this irreducible mismatch (a definition issue in
`B_coeff`/`recSum`, NOT a missing lemma). -/
theorem per_term (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t i1 : ℕ) (hi1 : i1 < t + 1 + 1)
    (lam : Nat.Partition (t + 1 - i1)) (hlam : (t + 1) ∉ lam.parts) :
    ∑ i ∈ (Finset.range ((Q x₀ R H).natDegree + 1)).filter (fun i => lam.parts.card ≤ i),
        liftToFunctionField (H:=H) ((evalX (C x₀) (hasseDerivX i1 R)).coeff i) *
          (i.choose lam.parts.card * lam.parts.countPerms) •
            (α₀ H ^ (i - lam.parts.card) *
              (Multiset.map (fun j => (PowerSeries.coeff j) (βHenselAssembled H x₀ R hHyp)) lam.parts).prod)
      = ClaimA2.ζ R x₀ H *
          (embeddingOf𝒪Into𝕃 H (W𝒪 H) ^ (i1 + deltaSave i1 - 1) *
                embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2) *
              embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam) *
            embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))) /
        (liftToFunctionField (H:=H) H.leadingCoeff ^ (t + 1 + 1) *
          embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * (t + 1) - 1)) := by
  rw [lhs_isum_collapse H x₀ R hHyp t i1 lam]
  rw [show (Multiset.map (fun j => (PowerSeries.coeff j) (βHenselAssembled H x₀ R hHyp)) lam.parts).prod
        = partitionProd lam (fun l => PowerSeries.coeff l (βHenselAssembled H x₀ R hHyp)) from rfl]
  rw [partitionProd_coeff_assembled H x₀ R hHyp lam]
  rw [brickE H x₀ R i1 lam.parts.card]
  rw [B_coeff, map_nsmul, embed_W𝒪, ClaimA2.embeddingOf𝒪Into𝕃_ξ]
  simp only [sigmaLambda, prefactor_eq_countPerms]
  rw [embeddingOf𝒪Into𝕃_mk]
  unfold hasseCoeffRepr𝒪
  rw [embeddingOf𝒪Into𝕃_mk]
  -- Bare goal: liftBivariate(cleared) (LHS) vs liftBivariate(p) (RHS) — structurally distinct.
  sorry

/-! ## The keystone, assembled from `per_term` (STEP 0–3 + congruence).
Compiles modulo `per_term` (and the verified `taylorCollapse` brick). -/
theorem keystone (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t := by
  unfold RestrictedFaaDiBrunoPartitionMatchAt restrictedFaaDiBrunoPartitionForm restrictedMatchRecursionPartitionForm
  simp only []
  rw [show PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp) = α₀ H by
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, βHenselAssembled_constantCoeff]]
  rw [Finset.sum_comm, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [sum_div', Finset.mul_sum, Nat.succ_eq_add_one]
  apply Finset.sum_congr rfl
  intro i1 hi1
  simp only [Finset.mem_range] at hi1
  rw [depSwap H (c := t + 1 - i1)
        (A := fun x => liftToFunctionField (H:=H) ((evalX (C x₀) (hasseDerivX i1 R)).coeff x))
        (g := fun x lam => (x.choose lam.parts.card * lam.parts.countPerms) •
              (α₀ H ^ (x - lam.parts.card) *
                (Multiset.map (fun j => (PowerSeries.coeff j) (βHenselAssembled H x₀ R hHyp)) lam.parts).prod))
        (Q := fun lam => (t + 1) ∉ lam.parts)]
  rw [mul_div_assoc', Finset.mul_sum]
  rw [div_eq_mul_inv, Finset.sum_mul]
  simp only [← div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro lam hlam
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam
  exact per_term H x₀ R hHyp t i1 hi1 lam hlam

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.bridge1_cleared
#print axioms BCIKS20.HenselNumerator.lhs_isum_collapse
#print axioms BCIKS20.HenselNumerator.keystone
