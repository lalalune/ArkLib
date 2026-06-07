/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2FubiniReabsorb
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RestrictedFaaDiBrunoXiTelescope
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.FaaDiBrunoBijectionPieces
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.UnclearedEmbedding

/-!
# BCIKS20 Appendix A.4 — the monic STEP-8 per-term Faà-di-Bruno identification (issue #139)

This file lands the **per-`(i₁,λ)` term identifications** that, for monic `H`, bridge the two sides
of the carved restricted Faà-di-Bruno match after the `W`-power and `ξ`-power obstructions have
collapsed.  All ingredients are P2-independent and axiom-clean.

## Where the two sides stand after the proven reductions

* LHS, fully reabsorbed (`restrictedFaaDiBrunoSum_eq_hasseDoubleSum`, PROVEN in
  `P2FubiniReabsorb`):
  `restrictedFaaDiBrunoSum … t = ∑_{ab ∈ antidiag(t+1)} ∑_{λ⊢ab.2, (t+1)∉λ}
      countPerms λ • (hasseEvalAtRoot ab.1 |λ| · ∏_{l∈λ} coeff l βHenselAssembled)`.
* RHS, monic, `W`-free and `ξ`-telescoped
  (`restrictedMatchRecursionPartitionForm_eq_ξfree_of_leadingCoeff_one`, PROVEN in
  `RestrictedFaaDiBrunoXiTelescope`):
  `restrictedMatchRecursionPartitionForm … t = ζ · ξ⁻¹ · ∑_{i₁∈range(t+2)} ∑_{λ⊢t+1-i₁, (t+1)∉λ}
      ⟦B_coeff i₁ λ⟧ · ⟦partitionProd λ βHensel⟧ / ξ^{2(t+1-i₁)-σλ}`.

## What this file proves (all axiom-clean)

* `embed_B_coeff_eq_countPerms_smul_hasseEvalAtRoot` — for general `H`, given the genuine
  `Y`-degree bound `natDegreeY ((Δ_X^{i₁} Δ_Y^{σλ} R)|x₀) ≤ R.natDegree − deltaSave i₁ − σλ`, the
  embedded recursion coefficient `⟦B_coeff i₁ λ⟧` equals `countPerms λ • (W^{k} · hasseEvalAtRoot
  i₁ σλ)` with `k = R.natDegree − deltaSave i₁ − σλ`.  This carries the genuine Y-Hasse content of
  `B_coeff` onto the same `hasseEvalAtRoot` object the LHS reabsorbs onto.
* `embed_B_coeff_eq_countPerms_smul_hasseEvalAtRoot_of_leadingCoeff_one` — the monic specialization
  (`W = 1` so `W^k = 1`): `⟦B_coeff i₁ λ⟧ = countPerms λ • hasseEvalAtRoot i₁ σλ`.  This is the
  **exact RHS counterpart of the LHS `countPerms λ • hasseEvalAtRoot i₁ |λ|` term**.
* `partitionProd_coeff_assembled_of_leadingCoeff_one` — the LHS per-term coefficient product, monic
  form: `∏_{l∈λ} coeff l βHenselAssembled = ⟦partitionProd λ βHensel⟧ / ξ^{2m−σλ}` (the `W`-power
  `W^{m+#λ}` collapses to `1`).  Its `ξ`-denominator `ξ^{2m−σλ}` is **exactly** the RHS per-term
  `ξ`-denominator `ξ^{2(t+1−i₁)−σλ}` once `m = t+1−i₁` (`sum_map_two_mul_sub_one`).
* `lhs_term_eq_countPerms_smul_hasseEvalAtRoot_mul_cleared_of_leadingCoeff_one` — the LHS per-term
  value in fully cleared monic shape, with both the `hasseEvalAtRoot` factor and the
  `⟦partitionProd⟧/ξ^{…}` factor exposed.
* `lhs_rhs_term_match_of_leadingCoeff_one` — the **per-`(i₁,λ)` term equality** for monic `H`,
  modulo the single global unit `ζ · ξ⁻¹`: the LHS term
  `countPerms λ • (hasseEvalAtRoot i₁ σλ · ∏ coeff l βHenselAssembled)` equals the RHS term
  `⟦B_coeff i₁ λ⟧ · ⟦partitionProd λ βHensel⟧ / ξ^{2(t+1−i₁)−σλ}`, **given the `B_coeff` degree
  bound**.  This is the term-by-term identification at the heart of the monic STEP-8 match; the
  remaining residual is the global `ζ · ξ⁻¹` unit reconciliation between the LHS double sum (no
  global unit) and the RHS (`ζ · ξ⁻¹ · (…)`), which is the genuine sign/discriminant-normalization
  content of BCIKS20 A.4.

See issue #139.
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

/-! ## 1. The embedded `B_coeff` carries the genuine `hasseEvalAtRoot` -/

/-- **Embedded `B_coeff` = `countPerms · W^k · hasseEvalAtRoot` (axiom-clean, general `H`).**
The genuine recursion coefficient `B_coeff i₁ λ = prefactor • ⟦cleared⟧` (with cleared exponent
`k = R.natDegree − deltaSave i₁ − σλ`) embeds — using the `W`-clearing embedding identity
`embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared` and `prefactor = countPerms` — to
`countPerms λ • (W^{k} · hasseEvalAtRoot i₁ σλ)`.  The `Y`-degree hypothesis is the genuine bound
on the specialized iterated-Hasse coefficient's `Y`-degree (cf. `hasseCoeffRepr𝒪_natDegreeY_le`);
it is exactly the side condition for the cleared embedding to be an honest polynomial image. -/
theorem embed_B_coeff_eq_countPerms_smul_hasseEvalAtRoot
    (x₀ : F) (R : F[X][X][Y]) (i1 : ℕ) {m : ℕ} (lam : Nat.Partition m)
    (hk : Bivariate.natDegreeY
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY (sigmaLambda lam) R)))
          ≤ R.natDegree - deltaSave i1 - sigmaLambda lam) :
    embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
      = lam.parts.countPerms
          • ((liftToFunctionField (H := H) H.leadingCoeff)
                ^ (R.natDegree - deltaSave i1 - sigmaLambda lam)
              * hasseEvalAtRoot H x₀ R i1 (sigmaLambda lam)) := by
  rw [B_coeff, prefactor_eq_countPerms, map_nsmul,
    embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared H x₀ R i1 (sigmaLambda lam)
      (R.natDegree - deltaSave i1 - sigmaLambda lam) hk]

/-- **Embedded `B_coeff` = `countPerms · hasseEvalAtRoot` for monic `H` (axiom-clean).**  When `H`
is monic the `W`-power `W^{k}` in `embed_B_coeff_eq_countPerms_smul_hasseEvalAtRoot` collapses to
`1`, so the embedded recursion coefficient is exactly `countPerms λ • hasseEvalAtRoot i₁ σλ` — the
**exact RHS counterpart** of the LHS reabsorbed term `countPerms λ • hasseEvalAtRoot i₁ |λ|`
(`restrictedFaaDiBrunoSum_eq_hasseDoubleSum`), since `σλ = sigmaLambda λ = λ.parts.card = |λ|`. -/
theorem embed_B_coeff_eq_countPerms_smul_hasseEvalAtRoot_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (i1 : ℕ) {m : ℕ} (lam : Nat.Partition m)
    (hlc : H.leadingCoeff = 1)
    (hk : Bivariate.natDegreeY
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY (sigmaLambda lam) R)))
          ≤ R.natDegree - deltaSave i1 - sigmaLambda lam) :
    embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
      = lam.parts.countPerms • hasseEvalAtRoot H x₀ R i1 (sigmaLambda lam) := by
  rw [embed_B_coeff_eq_countPerms_smul_hasseEvalAtRoot H x₀ R i1 lam hk,
    liftToFunctionField_leadingCoeff_eq_one_of_leadingCoeff_one H hlc, one_pow, one_mul]

/-! ## 2. The LHS per-term coefficient product, monic form -/

/-- **LHS per-term coefficient product, monic form (axiom-clean).**  For monic `H` the `W`-power
`W^{m+#λ}` in `partitionProd_coeff_assembled` collapses to `1`, leaving the pure `ξ`-cleared shape

  `∏_{l∈λ} coeff l βHenselAssembled = ⟦partitionProd λ βHensel⟧ / ξ^{∑_{l∈λ}(2l−1)}`.

By `sum_map_two_mul_sub_one`, `∑_{l∈λ}(2l−1) = 2m − σλ`, which (for `m = t+1−i₁`) is exactly the
per-term `ξ`-denominator exponent `2(t+1−i₁)−σλ` on the `ξ`-telescoped recursion side. -/
theorem partitionProd_coeff_assembled_of_leadingCoeff_one {m : ℕ} (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (lam : Nat.Partition m) (hlc : H.leadingCoeff = 1) :
    partitionProd lam (fun l => PowerSeries.coeff l (βHenselAssembled H x₀ R hHyp))
      = embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))
        / (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * m - sigmaLambda lam) := by
  rw [partitionProd_coeff_assembled H x₀ R hHyp lam,
    liftToFunctionField_leadingCoeff_eq_one_of_leadingCoeff_one H hlc, one_pow, one_mul,
    sum_map_two_mul_sub_one lam, sigmaLambda]

/-! ## 3. The per-`(i₁,λ)` term equality (modulo the global `ζ·ξ⁻¹` unit) -/

/-- **Per-`(i₁,λ)` LHS↔RHS term equality for monic `H` (axiom-clean, modulo the global unit).**
Combining the embedded-`B_coeff` identification
(`embed_B_coeff_eq_countPerms_smul_hasseEvalAtRoot_of_leadingCoeff_one`) and the LHS coefficient
product (`partitionProd_coeff_assembled_of_leadingCoeff_one`): the LHS reabsorbed term

  `countPerms λ • (hasseEvalAtRoot i₁ σλ · ∏_{l∈λ} coeff l βHenselAssembled)`

equals the `ξ`-telescoped RHS term

  `⟦B_coeff i₁ λ⟧ · ⟦partitionProd λ βHensel⟧ / ξ^{2m−σλ}`

with `m = ab.2`.  This is the genuine term-by-term Faà-di-Bruno identification for monic `H`: the
`countPerms`/`hasseEvalAtRoot` combinatorial data, the `partitionProd` value product, and the
`ξ`-denominator all match per term.  The only content **not** carried at the term level is the
single global unit `ζ · ξ⁻¹` (one per order), which is the BCIKS20 A.4 sign/discriminant
normalization reconciling the LHS double sum (no global unit) with the RHS (`ζ · ξ⁻¹ · (…)`). -/
theorem lhs_rhs_term_match_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (i1 : ℕ) {m : ℕ}
    (lam : Nat.Partition m) (hlc : H.leadingCoeff = 1)
    (hk : Bivariate.natDegreeY
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY (sigmaLambda lam) R)))
          ≤ R.natDegree - deltaSave i1 - sigmaLambda lam) :
    lam.parts.countPerms
        • (hasseEvalAtRoot H x₀ R i1 lam.parts.card
            * partitionProd lam (fun l => PowerSeries.coeff l (βHenselAssembled H x₀ R hHyp)))
      = embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
          * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))
          / (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * m - sigmaLambda lam) := by
  rw [embed_B_coeff_eq_countPerms_smul_hasseEvalAtRoot_of_leadingCoeff_one H x₀ R i1 lam hlc hk,
    partitionProd_coeff_assembled_of_leadingCoeff_one H x₀ R hHyp lam hlc]
  -- `σλ = lam.parts.card`, so the two `hasseEvalAtRoot` orders agree.
  show lam.parts.countPerms
      • (hasseEvalAtRoot H x₀ R i1 lam.parts.card
          * (embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))
              / (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * m - sigmaLambda lam)))
    = (lam.parts.countPerms • hasseEvalAtRoot H x₀ R i1 (sigmaLambda lam))
        * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))
        / (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * m - sigmaLambda lam)
  rw [sigmaLambda, nsmul_eq_mul, nsmul_eq_mul]
  ring

end BCIKS20.HenselNumerator

-- Axiom audit: every landed monic per-term identification is axiom-clean
-- (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`).
#print axioms BCIKS20.HenselNumerator.embed_B_coeff_eq_countPerms_smul_hasseEvalAtRoot
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.embed_B_coeff_eq_countPerms_smul_hasseEvalAtRoot_of_leadingCoeff_one
#print axioms BCIKS20.HenselNumerator.partitionProd_coeff_assembled_of_leadingCoeff_one
#print axioms BCIKS20.HenselNumerator.lhs_rhs_term_match_of_leadingCoeff_one
