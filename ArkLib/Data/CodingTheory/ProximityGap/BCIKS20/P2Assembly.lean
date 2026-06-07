/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2BijectionApply

/-!
# BCIKS20 Appendix A.4 — P2 assembly partition-form frontier (issue #139)

Both sides of the carved core `RestrictedFaaDiBrunoMatch` are now explicit partition sums, all
proven in `P2BijectionApply`:

* LHS — `restrictedFaaDiBrunoSum_eq_partitionForm`;
* RHS — `coeff_succ_βHenselAssembled_partitionForm` / `restrictedMatch_rhs_eq_recursionPartitionForm`
  (`-ζ · coeff(t+1)(βHenselAssembled) = ζ · recSum / den`);
* α₀-Taylor identity — `hasseEvalAtRoot_eq_taylorSum`;
* Y-Hasse commutation — `evalX_hasseDeriv_Y_coeff`.

The genuine combinatorial core of the per-term identification — the order-`k` Hasse-derivative
evaluation `(hasseDeriv k p).eval a = ∑_i C(i,k)·p.coeff i·a^{i-k}` — is proven independently as
`Polynomial.hasseDeriv_eval_eq_sum` (`ArkLib/ToMathlib/Polynomial/HasseDerivEval.lean`).

The remaining P2 obligation is the per-`(i₁,λ)` term-level equality assembling these into
`RestrictedFaaDiBrunoMatch`.  This file names the final partition-form residual and proves it is
equivalent to the carved core, so downstream work can target the exact normalized statement.
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

/-- The already-reindexed left side of the carved restricted Faà-di-Bruno match. -/
def restrictedFaaDiBrunoPartitionForm (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
    ∑ ab ∈ Finset.antidiagonal (t + 1),
      (liftToFunctionField (H := H)
          ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 R)).coeff i))
      * ∑ lam ∈ (Finset.univ : Finset (Nat.Partition ab.2)).filter
                  (fun lam => lam.parts.card ≤ i ∧ (t + 1) ∉ lam.parts),
          ((i.choose lam.parts.card) * lam.parts.countPerms)
            • ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - lam.parts.card)
                * (lam.parts.map (fun j =>
                    PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod)

/-- The already-normalized recursion-side right side of the carved restricted match. -/
def restrictedMatchRecursionPartitionForm (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  let recSum : 𝕃 H :=
    ∑ i1 ∈ Finset.range (t + 2),
      ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                (fun lam => (t + 1) ∉ lam.parts),
        embeddingOf𝒪Into𝕃 H (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
          * embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
          * embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
          * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))
  let den : 𝕃 H :=
    (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
      * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1)
  ClaimA2.ζ R x₀ H * (recSum / den)

/-- The final P2 partition-form residual: both sides of `RestrictedFaaDiBrunoMatch` after the
proven Faà-di-Bruno and recursion-side partition normalizations. -/
def RestrictedFaaDiBrunoPartitionMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) : Prop :=
  ∀ t : ℕ,
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t
      = restrictedMatchRecursionPartitionForm H x₀ R hHyp t

/-- Restatement of the proven left-side partition normalization using the named form. -/
theorem restrictedFaaDiBrunoSum_eq_restrictedPartitionForm (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    restrictedFaaDiBrunoSum H x₀ R hHyp t
      = restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t :=
  restrictedFaaDiBrunoSum_eq_partitionForm H x₀ R hHyp t

/-- Restatement of the proven right-side recursion normalization using the named form. -/
theorem restrictedMatch_rhs_eq_restrictedRecursionPartitionForm
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    - (ClaimA2.ζ R x₀ H
        * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp))
      = restrictedMatchRecursionPartitionForm H x₀ R hHyp t :=
  restrictedMatch_rhs_eq_recursionPartitionForm H x₀ R hHyp t

/-- The carved core is equivalent to the final partition-form residual. -/
theorem restrictedMatch_iff_partitionMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp
      ↔ RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp := by
  constructor
  · intro hmatch t
    rw [← restrictedFaaDiBrunoSum_eq_restrictedPartitionForm H x₀ R hHyp t,
      ← restrictedMatch_rhs_eq_restrictedRecursionPartitionForm H x₀ R hHyp t]
    exact hmatch t
  · intro hpart t
    rw [restrictedFaaDiBrunoSum_eq_restrictedPartitionForm H x₀ R hHyp t,
      restrictedMatch_rhs_eq_restrictedRecursionPartitionForm H x₀ R hHyp t]
    exact hpart t

-- In-file axiom audit for the named P2 partition residual and its equivalence to the carved core.
section AxiomAudit
#print axioms restrictedFaaDiBrunoPartitionForm
#print axioms restrictedMatchRecursionPartitionForm
#print axioms RestrictedFaaDiBrunoPartitionMatch
#print axioms restrictedFaaDiBrunoSum_eq_restrictedPartitionForm
#print axioms restrictedMatch_rhs_eq_restrictedRecursionPartitionForm
#print axioms restrictedMatch_iff_partitionMatch
end AxiomAudit

end BCIKS20.HenselNumerator
