/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Bijection

/-!
# BCIKS20 Appendix A.4 — `restrictedFaaDiBrunoSum` in partition form (toward `RestrictedFaaDiBrunoMatch`)

Applies the proven combinatorial reindex `innerSum_reindex` (`P2Bijection.lean`) to the actual
`restrictedFaaDiBrunoSum` (`P2Close.lean`): each guarded value-multiset inner sum becomes a sum over
partitions `λ` of `ab.2` with `≤ i` parts and no part `= t+1`.  This is the entropy-free half of
`RestrictedFaaDiBrunoMatch`; what remains is the algebraic identification of the partition-indexed
factors with the `(A.1)` recursion `βHensel_succ` (the `B_coeff` / Y-Hasse / `W`/`ξ`/`ζ` clearing).
-/

namespace BCIKS20.HenselNumerator

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **`restrictedFaaDiBrunoSum` in partition form.**  Rewrites the restricted Faà-di-Bruno defect
sum, term by term, into a sum over the Y-degree `i`, the `X`-Taylor split `ab`, and the partitions
`λ ⊢ ab.2` with `|λ| ≤ i` and `(t+1) ∉ λ`:

  `restrictedFaaDiBrunoSum t
     = ∑_i ∑_{ab} lift((Δ_X^{ab.1} R)|_{x₀}).coeff i ·
         ∑_{λ ⊢ ab.2, |λ|≤i, (t+1)∉λ} (C(i,|λ|)·countPerms λ) · (α₀^{i-|λ|} · ∏_{l∈λ} coeff l βHenselAssembled)`,

where `α₀ = coeff 0 βHenselAssembled`.  Pure application of `innerSum_reindex`. -/
theorem restrictedFaaDiBrunoSum_eq_partitionForm (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    restrictedFaaDiBrunoSum H x₀ R hHyp t
      = ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
          ∑ ab ∈ Finset.antidiagonal (t + 1),
            (liftToFunctionField (H := H)
                ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 R)).coeff i))
            * ∑ lam ∈ (Finset.univ : Finset (Nat.Partition ab.2)).filter
                        (fun lam => lam.parts.card ≤ i ∧ (t + 1) ∉ lam.parts),
                ((i.choose lam.parts.card) * lam.parts.countPerms)
                  • ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - lam.parts.card)
                      * (lam.parts.map (fun j =>
                          PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod) := by
  unfold restrictedFaaDiBrunoSum
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun ab _ => ?_))
  rw [innerSum_reindex i ab.2 (t + 1) (Nat.succ_pos t)
    (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))]

/-- **The `βHensel_succ` guard is vacuous on valid `(i₁,λ)`.**  In the `(A.1)` recursion the
partition product is `partitionProd λ (fun l => if l < t+1 then βHensel l else 0)`.  For `λ ⊢ (t+1−i₁)`
with `(t+1) ∉ λ`, every part `l` satisfies `l ≤ t+1−i₁` and `l ≠ t+1`, hence `l < t+1`, so the guard
is always taken and the product equals the plain `partitionProd λ (βHensel …)`. -/
theorem partitionProd_guard_eq (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t i1 : ℕ) (lam : Nat.Partition (t + 1 - i1)) (hT : (t + 1) ∉ lam.parts) :
    partitionProd lam (fun l => if _h : l < t + 1 then βHensel H x₀ R hHyp l else 0)
      = partitionProd lam (βHensel H x₀ R hHyp) := by
  unfold partitionProd
  congr 1
  apply Multiset.map_congr rfl
  intro l hl
  obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem hl
  have hle : l ≤ t + 1 - i1 := by
    have hsum : lam.parts.sum = l + rest.sum := by rw [hrest, Multiset.sum_cons]
    have : l ≤ lam.parts.sum := by rw [hsum]; exact Nat.le_add_right l rest.sum
    rwa [lam.parts_sum] at this
  have hne : l ≠ t + 1 := fun h => hT (h ▸ hl)
  rw [dif_pos (show l < t + 1 by omega)]

/-- **Embedding of the `(A.1)` recursion `βHensel (t+1)` into `𝕃 H`.**  Pushes the ring
homomorphism `embeddingOf𝒪Into𝕃` through `βHensel_succ` (sum, negation, products, powers) and
discharges the guard via `partitionProd_guard_eq`, giving the `(i₁,λ)` sum with the partition
product over the plain `βHensel`. -/
theorem embed_βHensel_succ (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
      = - ∑ i1 ∈ Finset.range (t + 2),
          ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                    (fun lam => (t + 1) ∉ lam.parts),
            embeddingOf𝒪Into𝕃 H (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
              * embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
              * embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
              * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp)) := by
  rw [βHensel_succ, map_neg, map_sum]
  refine congrArg Neg.neg (Finset.sum_congr rfl (fun i1 _ => ?_))
  rw [map_sum]
  refine Finset.sum_congr rfl (fun lam hlam => ?_)
  rw [partitionProd_guard_eq H x₀ R hHyp t i1 lam (Finset.mem_filter.mp hlam).2]
  simp only [map_mul, map_pow]

/-- **`coeff (t+1) βHenselAssembled` in `(i₁,λ)` partition form.**  Combines the definitional
`coeff_mk` unfolding of `βHenselAssembled` with `embed_βHensel_succ`: the order-`(t+1)` coefficient
is the embedded `(A.1)` recursion sum over `W^{t+2}·ξ^{2t+1}`.  Dual to
`restrictedFaaDiBrunoSum_eq_partitionForm`; together both sides of `RestrictedFaaDiBrunoMatch` are
now explicit partition sums, reducing the residual to a per-`(i₁,λ)` algebraic identity. -/
theorem coeff_succ_βHenselAssembled_partitionForm (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
      = (- ∑ i1 ∈ Finset.range (t + 2),
            ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                      (fun lam => (t + 1) ∉ lam.parts),
              embeddingOf𝒪Into𝕃 H (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
                * embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
                * embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
                * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp)))
        / ((liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1)) := by
  unfold βHenselAssembled
  rw [PowerSeries.coeff_mk, embed_βHensel_succ]

end BCIKS20.HenselNumerator

-- Axiom audit.
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoSum_eq_partitionForm
#print axioms BCIKS20.HenselNumerator.partitionProd_guard_eq
#print axioms BCIKS20.HenselNumerator.embed_βHensel_succ
#print axioms BCIKS20.HenselNumerator.coeff_succ_βHenselAssembled_partitionForm
