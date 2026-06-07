import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine
namespace BCIKS20.HenselNumerator
variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

theorem taylorCollapse (x₀ : F) (R : F[X][X][Y]) (i1 s : ℕ) :
  ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
    (i.choose s) • (liftToFunctionField (H:=H)
        ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i) * (α₀ H) ^ (i - s))
  = hasseEvalAtRoot H x₀ R i1 s := by sorry

-- BRICK E (local): hasseEvalAtRoot = emb(⟦cleared⟧)/W^N
lemma brickE (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    hasseEvalAtRoot H x₀ R i1 m
      = embeddingOf𝒪Into𝕃 H
          (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
            (hasseCoeffRepr𝒪_cleared H x₀ R i1 m) : 𝒪 H)
        / liftToFunctionField (H := H) H.leadingCoeff
            ^ Bivariate.natDegreeY
                (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))) := by
  rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared]
  rw [mul_comm, mul_div_assoc,
      div_self (pow_ne_zero _ (liftToFunctionField_leadingCoeff_ne_zero (H := H))), mul_one]

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
  -- factor out cp • P, leaving the taylorCollapse sum
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

-- Now the full per-term goal, attempting closure.
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
  -- LHS: cp • (hasseEvalAtRoot i1 card * P) where P = ∏ coeff_l
  -- rewrite P via partitionProd_coeff_assembled
  rw [show (Multiset.map (fun j => (PowerSeries.coeff j) (βHenselAssembled H x₀ R hHyp)) lam.parts).prod
        = partitionProd lam (fun l => PowerSeries.coeff l (βHenselAssembled H x₀ R hHyp)) from rfl]
  rw [partitionProd_coeff_assembled H x₀ R hHyp lam]
  -- rewrite hasseEvalAtRoot via BRICK E
  rw [brickE H x₀ R i1 lam.parts.card]
  -- RHS: expand B_coeff, embed ξ, W𝒪
  rw [B_coeff, map_nsmul]
  rw [embed_W𝒪, ClaimA2.embeddingOf𝒪Into𝕃_ξ]
  -- sigmaLambda lam = lam.parts.card
  simp only [sigmaLambda, prefactor_eq_countPerms]
  -- the cleared vs uncleared structural difference:
  -- LHS has emb(⟦cleared⟧)=liftBivariate(cleared); RHS has emb(hasseCoeffRepr𝒪)=liftBivariate(p).
  rw [embeddingOf𝒪Into𝕃_mk]  -- emb(⟦cleared⟧) = liftBivariate(cleared)
  unfold hasseCoeffRepr𝒪
  rw [embeddingOf𝒪Into𝕃_mk]  -- emb(hasseCoeffRepr𝒪) = liftBivariate(p)
  simp only [nsmul_eq_mul]
  field_simp
  ring

end BCIKS20.HenselNumerator
